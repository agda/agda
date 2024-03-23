{- | Bidirectional type checking of internal terms against some size type
 -   The goal of this process is to gather constraints between recursive calls,
 -   that later will be solved by some graph processing engine.
 -}
module Agda.Termination.TypeBased.Checking
  ( sizeCheckTerm
  ) where

import Control.Monad ( when, unless, zipWithM_ )
import Data.Foldable ( forM_, traverse_ )
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe ( fromJust, isJust )
import qualified Data.Set as Set

import Agda.Syntax.Common ( Induction(CoInductive), Arg(Arg) )
import Agda.Syntax.Internal ( QName, Elim'(IApply, Proj, Apply), PlusLevel'(Plus), Level'(Max), Sort'(UnivSort, Univ, PiSort, FunSort), Type''(unEl),
      Abs(Abs, NoAbs, unAbs), Elims, Term(..), ConHead(conName), Dom'(unDom), isSort )
import Agda.Termination.Common ( tryReduceNonRecursiveClause, buildRecCallLocation )
import Agda.Termination.Monad ( isCoinductiveProjection )
import Agda.Termination.TypeBased.Common ( applyDataType, sizeInstantiate, getDatatypeParametersByConstructor, tryReduceCopy )
import Agda.Termination.TypeBased.Encoding ( encodeFunctionType )
import Agda.Termination.TypeBased.Monad ( SConstraint(SConstraint), ConstrType(SLeq), getCurrentCoreContext, storeConstraint, reportCall, currentCheckedName, getRootArity, currentMutualNames,
      addFallbackInstantiation, reportDirectRecursion, storeBottomVariable, abstractCoreContext, freshenSignature, TBTM, markInfiniteSize, withVariableCounter, getSizePolarity )
import Agda.Termination.TypeBased.Syntax ( FreeGeneric(FreeGeneric, fgIndex), SizeType(..), Size(..), pattern UndefinedSizeType, sizeCodomain )
import Agda.TypeChecking.Monad.Base ( TCM, Definition(theDef, defCopy, defType, defSizedType), MonadTCM(liftTCM), pattern Constructor, conData, pattern Record,
      recInduction, pattern Function, funTerminates, isAbsurdLambdaName )
import Agda.TypeChecking.Monad.Debug ( reportSDoc )
import Agda.TypeChecking.Monad.Context ( AddContext(addContext) )
import Agda.TypeChecking.Monad.Signature ( HasConstInfo(getConstInfo), typeOfConst )
import Agda.TypeChecking.Pretty ( PrettyTCM(prettyTCM), pretty, nest, (<+>), vcat, text )
import Agda.TypeChecking.ProjectionLike ( ProjEliminator(EvenLone), elimView )
import Agda.TypeChecking.Polarity ( (\/), composePol, neg )
import Agda.TypeChecking.Polarity.Base ( Polarity(..) )
import Agda.TypeChecking.Reduce ( instantiate, reduce )
import Agda.TypeChecking.Telescope ( telView )
import Agda.TypeChecking.Substitute ( TelV(TelV) )
import Agda.Utils.Impossible ( __IMPOSSIBLE__ )

-- | Bidirectional-style checking of internal terms.
--   Though this function is checking, it also infers size types of terms,
--   because of the structure of the internal syntax in Agda (namely, because there are no explicit applications).
sizeCheckTerm :: SizeType -> Term -> TBTM SizeType
sizeCheckTerm tp term' = do
  -- Turn projection-like function into a sequence of projections
  unProjectedTerm <- liftTCM $ elimView EvenLone term'
  term <- liftTCM $ tryReduceCopy unProjectedTerm
  -- now the term is ready for size processing
  sizeCheckTerm' tp term

-- | The same as @sizeCheckTerm@, but acts on a sufficiently normalized terms.
--   It is enough for the term to be free from Agda's internal sugar, such as projection-like functions or copied definitions.
sizeCheckTerm' :: SizeType -> Term -> TBTM SizeType
sizeCheckTerm' expected t@(Var i elims) = do
  context <- getCurrentCoreContext
  case lookup i context of
    Nothing -> do
      reportSDoc "term.tbt" 80 $ vcat
        [ "Unknown variable" <+> prettyTCM t
        , "Where the context is" <+> pretty context
        ]
      _ <- sizeCheckEliminations UndefinedSizeType elims
      -- This branch is possible if the codomain of the processed function is large-eliminated.
      -- In this case, the pattern encoder can lose some variables.
      pure $ UndefinedSizeType
    Just sizeTypeOfVar -> do
      -- We need to freshen generic arguments, because each usage of a polymorphic variable implies new parameterization
      -- freshenedSizeType <- freshenGenericArguments sizeTypeOfVar
      reportSDoc "term.tbt" 20 $ vcat
        [ "Retrieving var" <+> prettyTCM t
        , "  Expected type             : " <+> pretty expected
        , "  Type of var (original)    : " <+> pretty sizeTypeOfVar
        ]
      reportSDoc "term.tbt" 60 $ vcat
        ["  Eliminations              : " <+> prettyTCM elims ]
      remainingCodomain <- case sizeTypeOfVar of
        Left freeGeneric -> sizeCheckEliminations UndefinedSizeType elims
        Right actualType -> sizeCheckEliminations actualType elims
      inferenceToChecking expected remainingCodomain
      case sizeTypeOfVar of
        Left freeGeneric ->
          -- From the theoretical point of view, it is wrong to return SizeGenericVar here,
          -- as there is no way to express the universe as the sized type. Hopefully, this will be fixed with the introduction of dependent types.
          -- However, this function is sometimes called from 'sizeCheckEliminations', which then proceeds with instantiating some generic parameter with
          -- the size type returned from this functions.
          -- So this hack here helps us to obtain a meaningful instantiation for that generic parameter, which would be UndefinedSizeTele otherwise.
          pure $ SizeGenericVar (length elims) (fgIndex freeGeneric)
        Right actualType -> pure $ remainingCodomain
sizeCheckTerm' expected t@(Def qn elims) = if isAbsurdLambdaName qn then pure UndefinedSizeType else do
  constInfo <- getConstInfo qn
  ((_, sizeSigOfDef), newSizeVariables) <- withVariableCounter $ resolveConstant qn
  reportSDoc "term.tbt" 20 $ vcat $
    [ "Retrieving definition " <> prettyTCM qn <> ":" ] ++ map (nest 2)
    [ "Term: " <+> prettyTCM t
    , "coreType: " <+> (prettyTCM =<< (typeOfConst qn))
    , "expected type: " <+> pretty expected
    , "Inferred size type of def:" <+> pretty sizeSigOfDef
    ]
  reportSDoc "term.tbt" 60 $ vcat
    [ "elims: " <+> prettyTCM elims
    , "is copy: " <+> text (show (defCopy constInfo))
    ]
  remainingCodomain <- sizeCheckEliminations sizeSigOfDef elims

  currentName <- currentCheckedName
  actualArgs <- if (currentName == qn)
    then do reportDirectRecursion newSizeVariables
            arity <- getRootArity
            let newCallArgs =take arity newSizeVariables
            forM_ (zip newCallArgs [0..arity - 1]) (uncurry addFallbackInstantiation)
            pure newCallArgs
    else pure newSizeVariables

  -- We need to record the occurrence of a possible size matrix at this place.
  maybeStoreRecursiveCall qn elims actualArgs

  reportSDoc "term.tbt" 40 $ "Eliminated type of " <> prettyTCM qn <> ": " <> pretty remainingCodomain
  inferenceToChecking expected remainingCodomain

  pure $ remainingCodomain
sizeCheckTerm' expected t@(Con ch ci elims) = do
  let (_, stCodomain) = sizeCodomain expected
  let constructorName = conName ch
  (constraints, tele) <- resolveConstant constructorName
  coinductive <- liftTCM $ isCoinductiveConstructor constructorName
  let actualConstraints =
        if coinductive
          -- Coinductive constructors are dual in some sense to inductive record projections, which means that the following definition:
          --
          -- record Stream (A : Set) : Set where
          --   constructor _,_
          --   coinductive
          --   field
          --     hd : A
          --     tl : A
          --
          -- foo : Stream Nat
          -- foo = 0 , foo
          --
          -- ...is fine from semantical point of view, but it destroys strong normalization. Hence we do not allow coinductive constructors to be considered guarding.
        then (\(SConstraint _ l r) -> [SConstraint SLeq l r, SConstraint SLeq r l]) =<< constraints
        else constraints
  forM_ actualConstraints storeConstraint
  when (null actualConstraints) $ do
    let (_, inferredCodomain) = sizeCodomain tele
    case inferredCodomain of
      -- The occurence of non-recursive constructor means that we have encountered a term that is not bigger than all parameters.
      SizeTree (SDefined i) _ -> storeBottomVariable i
      SizeTree (SUndefined) _ -> pure ()
      -- Since we are processing a constructor of an encoded data/record, we can expect a size tree as a codomain
      _ -> __IMPOSSIBLE__

  reportSDoc "term.tbt" 20 $ vcat $
    [ "Retrieving constructor" <+> prettyTCM constructorName <+> ":"] ++ map (nest 2)
    [ "term: " <+> prettyTCM t
    , "core type: " <+> (prettyTCM =<< typeOfConst constructorName)
    , "expected type: " <+> pretty expected
    , "Inferred size type of constructor:" <+> pretty tele
    , "constraints: " <+> text (show actualConstraints)
    ]
  reportSDoc "term.tbt" 60 $ vcat $
    [ "elims: " <+> prettyTCM elims
    ]

  -- Constructor type has a prepended telescope of enclosing module parameters and parameters of its datatype
  -- We need to apply this telescope to refine possible generics in the constructor type before actual elimination of constructor type.
  dataParameters <- liftTCM $ getDatatypeParametersByConstructor constructorName
  let initialConstructorArguments = case stCodomain of
        UndefinedSizeType -> replicate dataParameters UndefinedSizeType
        _ -> take dataParameters (unwrapSizeTree stCodomain)
  let preparedConstructorType = applyDataType initialConstructorArguments tele

  reportSDoc "term.tbt" 40 $ vcat $ map (nest 2)
    [ "constructor with applied data arguments:" <+> pretty preparedConstructorType
    ]
  remainingCodomain <- sizeCheckEliminations preparedConstructorType elims
  inferenceToChecking expected remainingCodomain
  pure $ remainingCodomain
sizeCheckTerm' _ (Level (Max _ ls)) = do
  traverse_ (sizeCheckTerm UndefinedSizeType . (\(Plus _ i) -> i)) ls
  pure UndefinedSizeType
sizeCheckTerm' expected t@(Lam info tm) = do
  reportSDoc "term.tbt" 20 $ vcat
    [ "Dispatching into lambda expression"
    , "  Expected size type: " <+> pretty expected
    ]
  let (argSizeType, rest) = case expected of
        SizeArrow pt rest -> (Right pt, rest)
        SizeGeneric args rest -> (Left (FreeGeneric args 0), rest)
        UndefinedSizeType -> (Right UndefinedSizeType, UndefinedSizeType)
        _ -> __IMPOSSIBLE__
  case tm of
    Abs arg tm -> do
      -- We still need to maintain internal context to get pretty-printed termination errors
      checkedTerm <- abstractCoreContext 0 argSizeType $ addContext arg $ sizeCheckTerm rest tm
      pure $ SizeArrow UndefinedSizeType checkedTerm
    NoAbs _ tm -> do
      sizeCheckTerm rest tm
sizeCheckTerm' _ (Pi _ _) = pure $ UndefinedSizeType
sizeCheckTerm' expected t@(MetaV _ el) = do
  inst <- liftTCM $ instantiate t
  case inst of
    MetaV _ _ -> pure $ UndefinedSizeType
    t -> sizeCheckTerm expected t
sizeCheckTerm' _ (Lit _) = pure $ UndefinedSizeType -- todo
sizeCheckTerm' _ (Sort s) = case s of
  Univ _ l -> sizeCheckTerm UndefinedSizeType (Level l)
  PiSort d i r -> do
    _ <- sizeCheckTerm UndefinedSizeType (unDom d)
    _ <- sizeCheckTerm UndefinedSizeType (Sort i)
    _ <- sizeCheckTerm UndefinedSizeType (Sort (unAbs r))
    pure UndefinedSizeType
  FunSort f s -> do
    _ <- sizeCheckTerm UndefinedSizeType (Sort f)
    _ <- sizeCheckTerm UndefinedSizeType (Sort s)
    pure UndefinedSizeType
  UnivSort t -> do
    _ <- sizeCheckTerm UndefinedSizeType (Sort t)
    pure UndefinedSizeType
  _ -> pure UndefinedSizeType
sizeCheckTerm' expected (DontCare t) = sizeCheckTerm' expected t
sizeCheckTerm' _ (Dummy _ _) = pure $ UndefinedSizeType

maybeStoreRecursiveCall :: QName -> Elims  -> [Int] -> TBTM ()
maybeStoreRecursiveCall qn elims callSizes = do
  names <- currentMutualNames
  tryReduceNonRecursiveClause qn elims names (\_ -> reportSDoc "term.tbt" 80 "Call is reduced away")
    (do
      rootArity <- getRootArity
      let rootFunctionSizes =  [0..(rootArity - 1)]
      storeCall qn rootFunctionSizes callSizes elims
    )

-- | Records the constraints obtained from comparing inferred and checked size types.
-- This is more or less standard transition from checking to inference in bidirectional type checking.
inferenceToChecking :: SizeType -> SizeType -> TBTM ()
inferenceToChecking expected inferred = unless (expected == UndefinedSizeType) $ smallerOrEq Covariant inferred expected

-- | We cannot do argument checking in a straightforward zip-loop, because an instantiation of a generic may unlock new possibility for elimination.
-- Example : `apply foo a b`, where `apply : (A -> B) -> A -> B` and `foo : C -> D -> E`. Here instantiation of `B` is `D -> E`, which unlocks the application of `b`.
-- Returns the residual codomain in the end of the list.
-- This is analogous to @checkSpine@ in the double checker.
sizeCheckEliminations :: SizeType -> Elims -> TBTM SizeType
sizeCheckEliminations eliminated [] = pure eliminated
sizeCheckEliminations eliminated@UndefinedSizeType (elim : elims) = do
  arg <- case elim of
    Apply (Arg _ t) -> sizeCheckTerm UndefinedSizeType t
    _ -> pure $ UndefinedSizeType
  sizeCheckEliminations eliminated elims
sizeCheckEliminations eliminated (elim : elims) = do
  reportSDoc "term.tbt" 80 $ "Eliminating a type" <+> vcat
    [ "full sizeType to eliminate:   " <+> pretty eliminated
    , "currently applied elimination:" <+> prettyTCM elim
    ]
  case (elim, eliminated) of
    (Proj _ qname, eliminatedRecord@(SizeTree root args)) -> do
      (inferredRecordType, projectionCodomain) <- eliminateProjection qname eliminatedRecord (map snd args)
      sizeCheckEliminations projectionCodomain elims
    (Apply (Arg _ t), SizeGenericVar args i) -> do
      _ <- sizeCheckTerm UndefinedSizeType t
      sizeCheckEliminations (SizeGenericVar (args + 1) i) elims
    (Apply (Arg _ t), SizeGeneric arity rest) -> do
      checkedDomain <- case t of
        -- Unfortunately, we have to apply counter-measures for Set-valued functions and do reductions, since we work in System F,
        -- and the internal syntax is written in dependent types.
        -- If we don't do it, then typealiases will be invisible for our termination checker.
        -- I conjecture that all these reductions happen on type-level (well, most of them), so they should not slow down the system significantly.
        (Def qn _) -> do
          reportSDoc "term.tbt" 80 $ "Attempting reduction during elimination of " <+> prettyTCM qn
          def <- getConstInfo qn
          TelV _ codomain <- liftTCM $ telView (defType def)
          term <- if (isJust . isSort . unEl $ codomain) && isTerminatingDefinition def
            then liftTCM $ tryReduceCopy =<< reduce t
            else pure t
          case term of
            Def qn _ -> do
              copy <- defCopy <$> getConstInfo qn
              reportSDoc "term.tbt" 80 $ "Is reduced definition copied:" <+> text (show copy)
            _ -> pure ()
          sizeCheckTerm UndefinedSizeType term
        _ -> sizeCheckTerm UndefinedSizeType t
      let inst = sizeInstantiate checkedDomain rest
      sizeCheckEliminations inst elims
    (Apply (Arg _ t), SizeArrow arg rest) -> do
      checkedDomain <- sizeCheckTerm arg t
      sizeCheckEliminations rest elims
    (Proj _ t, tele) -> __IMPOSSIBLE__
    (Apply (Arg _ t), _) -> do
      reportSDoc "term.tbt" 20 $ vcat
        [ "Elimination of unsupported size type:"
        , "elim: " <+> prettyTCM elim
        , "expected size type: " <+> pretty eliminated
        ]
      __IMPOSSIBLE__
    (IApply _ _ _, _) -> __IMPOSSIBLE__

-- | Eliminates projection, returns inferred type of eliminated record and the residual inferred codomain of projection.
eliminateProjection :: QName -> SizeType -> [SizeType] -> TBTM (SizeType, SizeType)
eliminateProjection projName eliminatedRecord recordArgs = do
  (constraints, projectionType) <- resolveConstant projName
  isCoinductive <- isCoinductiveProjection True projName
  let actualConstraints =
        if isCoinductive
        then constraints
        -- In Agda, inductive projections are treated as size-preserving by the syntax-based checker.
        -- The reason is that it is valid to have a mutually defined inductive record and inductive datatype,
        -- where the functions defined on the inductive record may use projections.
        -- For example, the following code is valid:
        --
        -- mutual
        --   record R : Set where
        --   inductive
        --   field force : D
        --
        --   data D : Set where
        --     d : R → D
        --
        -- open R
        --
        -- foo : R → R
        -- bar : D → R
        -- bar (d r) = foo r
        -- foo r = bar (force r)
        --
        -- The functions defined above are strongly normalizing.
        -- However, we should not treat inductive projections as size-decreasing, as it would permit the following snippet to pass the termination check:
        --
        --  record R : Set where
        --    inductive
        --    field force : R
        --
        --  foo : R → R
        --  foo r = foo (R.force r)
        --
        -- If we interpret inductive records as the least fixpoints, then from semantical point of view the code above terminates.
        -- But we treat function definitions as rewrite rules, hence the code above can be unfolded infinitely, which destroys strong normalization of our system.
        -- This would have a nasty consequence of making Agda's type checker loop.
        -- The cure here is to treat inductive projections as size-preserving, and not size-decreasing,
        -- as it requires to do eventual pattern-matching on inductive type to block the unfolding of functions that involve inductive record.
        else (\(SConstraint _ from to) -> [SConstraint SLeq from to, SConstraint SLeq to from]) =<< constraints
  forM_ actualConstraints storeConstraint
  reportSDoc "term.tbt" 20 $ vcat $ ["Eliminating projection:" <+> prettyTCM projName] ++ map (nest 2)
    [ "of type: " <+> pretty projectionType
    , "with record carrier: " <+> pretty eliminatedRecord
    ]
  reportSDoc "term.tbt" 60 $ vcat $ map (nest 2) $
    [ "and constraints: " <+> (text (show actualConstraints))
    , "record args: " <+> pretty recordArgs
    ]
  let inferredProjectionType = applyDataType recordArgs projectionType
  reportSDoc "term.tbt" 40 $ "  Applied projection type: " <+> pretty inferredProjectionType
  case inferredProjectionType of
    SizeArrow inferredRecordDef restDef -> do
      -- The order here is a bit tricky.
      -- One may argue that `eliminatedRecord` comes from the position of expected type, which means that it should be "bigger" than its argument.
      -- However, in this case we are not _eliminating a record (datatype) with a projection (function)_,
      -- we are _eliminating a projection (function) with a record (argument to a function)_.
      -- It means that the inferred first parameter of projection actually becomes the expected type of the record.
      smallerOrEq Covariant eliminatedRecord inferredRecordDef
      pure (inferredRecordDef, restDef)
    UndefinedSizeType -> pure (UndefinedSizeType, UndefinedSizeType)
    _ -> __IMPOSSIBLE__


-- | Compares two size types and stores the obtained constraints.
smallerOrEq :: Polarity -> SizeType -> SizeType -> TBTM ()
smallerOrEq pol (SizeTree s1 tree1) (SizeTree s2 tree2) = do
  p1 <- getSizePolarity s1
  p2 <- getSizePolarity s2
  reportSDoc "term.tbt" 40 $ vcat
    [ "Comparing size trees:" <+> pretty (SizeTree s1 tree1) <+> "<=" <+> pretty (SizeTree s2 tree2)
    , "with polarities: " <+> pretty p1 <+> " and " <+> pretty p2
    , "and main polarity: " <+> pretty pol
    ]
  let argPol = p1 \/ p2
  let prodPol = composePol pol argPol
  smallerSize prodPol s1 s2

  zipWithM_ (\(p1, t1) (p2, t2) -> smallerOrEq (composePol (p1 \/ p2) pol) t1 t2) tree1 tree2
  where
    smallerSize :: Polarity -> Size -> Size -> TBTM ()
    smallerSize Contravariant t1 t2 = smallerSize Covariant t2 t1
    smallerSize Invariant t1 t2 = smallerSize Covariant t1 t2 >> smallerSize Covariant t2 t1
    smallerSize Nonvariant t1 t2 = pure ()
    smallerSize Covariant (SDefined i1) (SDefined i2) = do
      reportSDoc "term.tbt" 40 $ "Registering:" <+> pretty (SDefined i1) <+> "<=" <+> pretty (SDefined i2)
      storeConstraint (SConstraint SLeq i1 i2)
    smallerSize Covariant SUndefined (SDefined i) = do
      reportSDoc "term.tbt" 40 $ "Marking size variable as undefined, because it has lower bound of infinity: " <+> pretty (SDefined i)
      markInfiniteSize i
    smallerSize Covariant t SUndefined =
      -- It is okay to have infinity as an upper bound
      pure ()
smallerOrEq _ UndefinedSizeType _ = pure ()
smallerOrEq _ _ UndefinedSizeType = pure ()
smallerOrEq pol t1@(SizeGenericVar args1 i1) t2@(SizeGenericVar args2 i2) =
  when (i1 == i2 && args1 /= args2) $ do
    reportSDoc "term.tbt" 20 $ vcat
      ["Attempt to compare incomparable generic variables:"
      , "t1: " <+> pretty t1
      , "t2: " <+> pretty t2
      ]
    __IMPOSSIBLE__
smallerOrEq pol (SizeArrow d1 c1) (SizeArrow d2 c2) = smallerOrEq (neg pol) d1 d2 >> smallerOrEq pol c1 c2 -- note the contravariance in domain
smallerOrEq pol (SizeGeneric _ rest1) (SizeGeneric _ rest2) = smallerOrEq pol rest1 rest2
smallerOrEq pol (SizeGeneric _ rest1) (SizeArrow UndefinedSizeType rest2) = smallerOrEq pol (sizeInstantiate UndefinedSizeType rest1) rest2
smallerOrEq pol (SizeArrow UndefinedSizeType rest1) (SizeGeneric _ rest2) = smallerOrEq pol rest1 (sizeInstantiate UndefinedSizeType rest2)
smallerOrEq pol (SizeTree _ _) (SizeArrow _ _) = pure () -- can occur, becase encoding of terms is intentionaly not complete
smallerOrEq pol (SizeArrow _ _) (SizeTree _ _) = pure ()
smallerOrEq pol (SizeArrow _ r) (SizeGenericVar args i) = smallerOrEq pol r (SizeGenericVar (args + 1) i) -- eta-conversion
smallerOrEq pol (SizeGenericVar args i) (SizeArrow _ r) = smallerOrEq pol (SizeGenericVar (args + 1) i) r -- eta-conversion
smallerOrEq pol t1 t2 = do
  -- One example of a problem is an attempt to compare generic var and size variable.
  -- This is an internal error, because it means that there is a forgotten instantiation somewhere.
  reportSDoc "term.tbt" 20 $ vcat
    ["Attempt to compare incomparable terms:"
    , "t1: " <+> pretty t1
    , "t2: " <+> pretty t2
    , "polarity: " <+> pretty pol
    ]
  __IMPOSSIBLE__


-- | Retrieves sized type for a constant
-- May return Nothing for primitive definition
resolveConstant :: QName -> TBTM ([SConstraint], SizeType)
resolveConstant nm = do
  currentName <- currentCheckedName
  constInfo <- getConstInfo nm
  sizedSig <- if currentName == nm
    then do
      let currentType = defType constInfo
      liftTCM $ encodeFunctionType currentType
    else pure $ defSizedType constInfo
  let startingPolarity = case theDef constInfo of
        Function {} -> Covariant
        _ -> Invariant
  freshenSignature startingPolarity sizedSig

-- | Record information about a recursive call from current function to q2
--   Only the calls withing the same mutual block matter.
storeCall :: QName -> [Int] -> [Int] -> Elims -> TBTM ()
storeCall q2 sizesq1 sizesq2 elims = do
  names <- currentMutualNames
  when (q2 `Set.member` names) do
    currentName <- currentCheckedName
    reportSDoc "term.tbt" 10 $ vcat
      [ "Detected mutual-recursive call"
      , "  From '" <> prettyTCM currentName <> "' with size variables: " <> text (show sizesq1)
      , "  To   '" <> prettyTCM q2 <> "' with size variables: " <> text (show sizesq2)
      ]
    doc <- buildRecCallLocation q2 elims
    reportCall q2 sizesq1 sizesq2 doc

unwrapSizeTree :: SizeType -> [SizeType]
unwrapSizeTree (SizeTree _ ts) = map snd ts
unwrapSizeTree t = __IMPOSSIBLE__

isTerminatingDefinition :: Definition -> Bool
isTerminatingDefinition d = case theDef d of
  Function{ funTerminates } | funTerminates == Just True -> True
  _ -> False

isCoinductiveConstructor :: QName -> TCM Bool
isCoinductiveConstructor qn = do
  def <- theDef <$> getConstInfo qn
  case def of
    Constructor { conData } -> do
      dataInfo <- theDef <$> getConstInfo conData
      case dataInfo of
        Record { recInduction = Just CoInductive } -> pure True
        _ -> pure False
    _ -> pure False

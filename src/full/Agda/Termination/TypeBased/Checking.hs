{- | Bidirectional type checking of internal terms against some size type
 -   The goal of this process is to gather constraints between recursive calls,
 -   that later will be solved by some graph processing engine.
 -}
module Agda.Termination.TypeBased.Checking where

import Agda.Syntax.Internal
import Agda.Termination.TypeBased.Syntax
import Control.Monad.Trans.State
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Statistics
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Signature
import Agda.Syntax.Common
import qualified Data.Map as Map
import Data.Map ( Map )
import qualified Data.IntMap as IntMap
import Data.IntMap ( IntMap )
import qualified Data.IntSet as IntSet
import Data.IntSet ( IntSet )
import qualified Data.Set as Set
import Data.Set ( Set )
import qualified Data.List as List
import Agda.Syntax.Abstract.Name
import Control.Monad.IO.Class
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Telescope
import Agda.Termination.TypeBased.Common
import Agda.TypeChecking.Substitute
import Agda.Termination.TypeBased.Monad
import Agda.TypeChecking.ProjectionLike
import Agda.Utils.Impossible
import Control.Monad
import Agda.TypeChecking.Pretty
import Agda.Termination.TypeBased.Common
import Agda.Utils.Monad
import Agda.Termination.Common
import Data.Maybe
import Agda.Termination.TypeBased.Encoding
import Data.Functor
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty(..), (<|))
import Agda.Termination.Monad (isCoinductiveProjection)

-- | Bidirectional-style checking of internal terms.
--   Though this function is checking, it also infers size types of terms,
--   because of the structure of the internal syntax in Agda (namely, because there are no explicit applications).
sizeCheckTerm :: SizeType -> Term -> MonadSizeChecker SizeType
sizeCheckTerm tp term' = do
  -- Turn projection-like function into a sequence of projections
  unProjectedTerm <- MSC $ elimView EvenLone term'
  term <- liftTCM $ tryReduceCopy unProjectedTerm
  -- now the term is ready for size processing
  sizeCheckTerm' tp term

-- | The same as @sizeCheckTerm@, but acts on a sufficiently normalized terms.
--   It is enough for the term to be free from Agda's internal sugar, such as projection-like functions or copied definitions.
sizeCheckTerm' :: SizeType -> Term -> MonadSizeChecker SizeType
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
  -- New size variables in a freshened definitions are those that were populated during the freshening. Yes, a bit of an abstraction leak, TODO
  currentSizeLimit <- MSC $ gets scsFreshVarCounter
  constInfo <- getConstInfo qn
  sizeSigOfDef <- resolveConstant qn
  case sizeSigOfDef of
    Nothing -> do
      reportSDoc "term.tbt" 80 $ "No size type for definition" <+> prettyTCM qn
      pure $ UndefinedSizeType
    -- This definition is a function, which has no interesting size bounds, so we can safely ignore them
    Just (_, sizeTypeOfDef) -> do
      newSizeVariables <- MSC (gets scsFreshVarCounter) <&> \x -> [currentSizeLimit .. (x - 1)]
      let (_, scodomain) = sizeCodomain sizeTypeOfDef
      reportSDoc "term.tbt" 20 $ vcat $
        [ "Retrieving definition " <> prettyTCM qn <> ":" ] ++ map (nest 2)
        [ "Term: " <+> prettyTCM t
        , "coreType: " <+> (prettyTCM =<< (typeOfConst qn))
        , "expected type: " <+> pretty expected
        , "Inferred size type of def:" <+> pretty sizeTypeOfDef
        ]
      reportSDoc "term.tbt" 60 $ vcat
        [ "elims: " <+> prettyTCM elims
        , "is copy: " <+> text (show (defCopy constInfo))
        ]
      remainingCodomain <- sizeCheckEliminations sizeTypeOfDef elims

      -- We need to record the occurrence of a possible size matrix at this place.
      maybeStoreRecursiveCall qn elims newSizeVariables

      reportSDoc "term.tbt" 40 $ "Eliminated type of " <> prettyTCM qn <> ": " <> pretty remainingCodomain
      inferenceToChecking expected remainingCodomain

      pure $ remainingCodomain
sizeCheckTerm' expected t@(Con ch ci elims) = do
  let (_, stCodomain) = sizeCodomain expected
  let constructorName = conName ch
  (constraints, tele) <- fromJust <$> resolveConstant constructorName
  forM_ constraints storeConstraint
  let isNonRecursive = null constraints
  let (_, inferredCodomain) = sizeCodomain tele
  when isNonRecursive $ case inferredCodomain of
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
sizeCheckTerm' _ (Level _) = pure $ UndefinedSizeType -- TODO
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
  inst <- MSC $ instantiate t
  case inst of
    MetaV _ _ -> pure $ UndefinedSizeType
    t -> sizeCheckTerm expected t
sizeCheckTerm' _ (Lit _) = pure $ UndefinedSizeType -- todo
sizeCheckTerm' _ (Sort _) = pure $ UndefinedSizeType
sizeCheckTerm' _ (DontCare _) = pure $ UndefinedSizeType
sizeCheckTerm' _ (Dummy _ _) = pure $ UndefinedSizeType

maybeStoreRecursiveCall :: QName -> Elims  -> [Int] -> MonadSizeChecker ()
maybeStoreRecursiveCall qn elims callSizes = do
  names <- currentMutualNames
  tryReduceNonRecursiveClause qn elims names (\_ -> reportSDoc "term.tbt" 80 "Call is reduced away")
    (do
      currentSymbol <- currentCheckedName
      rootArity <- getRootArity
      let rootFunctionSizes =  [0..(rootArity - 1)]
      storeCall currentSymbol qn rootFunctionSizes callSizes elims
    )

-- | Records the constraints obtained from comparing inferred and checked size types.
-- This is more or less standard transition from checking to inference in bidirectional type checking.
inferenceToChecking :: SizeType -> SizeType -> MonadSizeChecker ()
inferenceToChecking expected inferred = unless (expected == UndefinedSizeType) $ inferred `smallerOrEq` expected

datatypeArguments :: Int -> SizeType -> Int
datatypeArguments fallback (SizeTree _ args) = length args
datatypeArguments fallback _ = fallback

-- | This size signature carries zero information. Effectively erases all information about the types.
isDumbType :: SizeType -> Bool
isDumbType (SizeTree SUndefined []) = True
isDumbType _ = False


-- | We cannot do argument checking in a straightforward zip-loop, because an instantiation of a generic may unlock new possibility for elimination.
-- Example : `apply foo a b`, where `apply : (A -> B) -> A -> B` and `foo : C -> D -> E`. Here instantiation of `B` is `D -> E`, which unlocks the application of `b`.
-- Returns the residual codomain in the end of the list.
-- This is analogous to @checkSpine@ in the double checker.
sizeCheckEliminations :: SizeType -> Elims -> MonadSizeChecker SizeType
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
      (inferredRecordType, projectionCodomain) <- eliminateProjection qname eliminatedRecord args
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
          TelV _ codomain <- MSC $ telView (defType def)
          term <- if (isJust . isSort . unEl $ codomain) && isTerminatingDefinition def
            then liftTCM . tryReduceCopy =<< MSC (reduce t)
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
eliminateProjection :: QName -> SizeType -> [SizeType] -> MonadSizeChecker (SizeType, SizeType)
eliminateProjection projName eliminatedRecord recordArgs = do
  (constraints, projectionType) <- fromJust <$> resolveConstant projName
  forM_ constraints storeConstraint
  -- The use of projections on inductive records create decrease in sizes.
  -- This is supported by the syntax-based termination checker,
  -- and we don't want to have any regressions regarding termination checking.
  -- It may be the case that there is no suitable size variable in the environment
  -- (i.e. the clause has the form `foo x = foo (x .proj)`, where `x`'s type is an inductive record)
  -- which means that we have to add a new rigid during the checking of the body.
  -- This ruins the elegance of graph solver later, since a bound of this rigid variable is not another rigid.
  case constraints of
    [x] -> do
      -- We do not want to create a rigid variable if there is a coinductive projection,
      -- since this makes coinductive functions trivially terminating.
      coinductive <- isCoinductiveProjection True projName
      unless coinductive $ do
        reportSDoc "term.tbt" 40 $ "Adding new rigid:" <+> text (show x)
        addNewRigid (scFrom x) (SizeBounded (scTo x))
    _ -> pure ()
  reportSDoc "term.tbt" 20 $ vcat $ ["Eliminating projection:" <+> prettyTCM projName] ++ map (nest 2)
    [ "of type: " <+> pretty projectionType
    , "with record carrier: " <+> pretty eliminatedRecord
    ]
  reportSDoc "term.tbt" 60 $ vcat $ map (nest 2) $
    [ "and constraints: " <+> (text (show constraints))
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
      eliminatedRecord `smallerOrEq` inferredRecordDef
      pure (inferredRecordDef, restDef)
    UndefinedSizeType -> pure (UndefinedSizeType, UndefinedSizeType)
    _ -> __IMPOSSIBLE__


-- | Compares two size types and stores the obtained constraints.
--   The idea is that during the later computation of assignment for flexible types,
--   all these constraints should be respected.
smallerOrEq :: SizeType -> SizeType -> MonadSizeChecker ()
smallerOrEq (SizeTree s1 tree1) (SizeTree s2 tree2) = do
  ifM (isContravariant s1 `or2M` isContravariant s2) {- then -} (smallerSize s2 s1) {- else -} (smallerSize s1 s2)
  zipWithM_ smallerOrEq tree1 tree2
  where
    smallerSize :: Size -> Size -> MonadSizeChecker ()
    smallerSize (SDefined i1) (SDefined i2) = do
      reportSDoc "term.tbt" 40 $ "Registering:" <+> pretty (SDefined i1) <+> "<=" <+> pretty (SDefined i2)
      storeConstraint (SConstraint SLeq i1 i2)
    smallerSize SUndefined (SDefined i) = do
      reportSDoc "term.tbt" 40 $ "Marking size variable as undefined, because it has lower bound of infinity: " <+> pretty (SDefined i)
      markUndefinedSize i
    smallerSize _ _ = pure ()
smallerOrEq (UndefinedSizeType) _ = pure ()
smallerOrEq _ (UndefinedSizeType) = pure ()
smallerOrEq t1@(SizeGenericVar args1 i1) t2@(SizeGenericVar args2 i2) =
  when (i1 == i2 && args1 /= args2) $ do
    reportSDoc "term.tbt" 20 $ vcat
      ["Attempt to compare incomparable generic variables:"
      , "t1: " <+> pretty t1
      , "t2: " <+> pretty t2
      ]
    __IMPOSSIBLE__
smallerOrEq (SizeArrow d1 c1) (SizeArrow d2 c2) = d2 `smallerOrEq` d1 >> c1 `smallerOrEq` c2 -- note the contravariance in domain
smallerOrEq (SizeGeneric _ rest1) (SizeGeneric _ rest2) = smallerOrEq rest1 rest2
smallerOrEq (SizeGeneric _ rest1) (SizeArrow UndefinedSizeType rest2) = smallerOrEq (sizeInstantiate UndefinedSizeType rest1) rest2
smallerOrEq (SizeArrow UndefinedSizeType rest1) (SizeGeneric _ rest2) = smallerOrEq rest1 (sizeInstantiate UndefinedSizeType rest2)
smallerOrEq (SizeTree _ _) (SizeArrow _ _) = pure () -- can occur, becase encoding of terms is intentionaly not complete
smallerOrEq (SizeArrow _ _) (SizeTree _ _) = pure ()
smallerOrEq (SizeArrow _ r) (SizeGenericVar args i) = r `smallerOrEq` (SizeGenericVar (args + 1) i) -- eta-conversion
smallerOrEq (SizeGenericVar args i) (SizeArrow _ r) = (SizeGenericVar (args + 1) i) `smallerOrEq` r -- eta-conversion
smallerOrEq t1 t2 = do
  -- One example of a problem is an attempt to compare generic var and size variable.
  -- This is an internal error, because it means that there is a forgotten instantiation somewhere.
  reportSDoc "term.tbt" 20 $ vcat
    ["Attempt to compare incomparable terms:"
    , "t1: " <+> pretty t1
    , "t2: " <+> pretty t2
    ]
  __IMPOSSIBLE__


-- | Retrieves sized type for a constant
-- May return Nothing for primitive definition
resolveConstant :: QName -> MonadSizeChecker (Maybe ([SConstraint], SizeType))
resolveConstant nm = do
  sizedSig <- defSizedType <$> getConstInfo nm
  case sizedSig of
    Nothing -> pure Nothing
    Just sig -> Just <$> freshenSignature sig

-- | Record information about a recursive call from q1 to q2
--   Only the calls withing the same mutual block matter.
storeCall :: QName -> QName -> [Int] -> [Int] -> Elims -> MonadSizeChecker ()
storeCall q1 q2 sizesq1 sizesq2 elims = do
  names <- currentMutualNames
  when (q1 `Set.member` names && q2 `Set.member` names) do
    reportSDoc "term.tbt" 10 $ vcat
      [ "Detected mutual-recursive call"
      , "  From '" <> prettyTCM q1 <> "' with size variables: " <> text (show sizesq1)
      , "  To   '" <> prettyTCM q2 <> "' with size variables: " <> text (show sizesq2)
      ]
    doc <- buildRecCallLocation q2 elims
    reportCall q1 q2 sizesq1 sizesq2 doc
    when (q1 == q2) $ do
      forM_ (zip sizesq2 sizesq1) (uncurry addFallbackInstantiation)
      reportDirectRecursion sizesq2

unwrapSizeTree :: SizeType -> [SizeType]
unwrapSizeTree (SizeTree _ ts) = ts
unwrapSizeTree t = __IMPOSSIBLE__

isTerminatingDefinition :: Definition -> Bool
isTerminatingDefinition d = case theDef d of
  Function{ funTerminates } | funTerminates == Just True -> True
  _ -> False

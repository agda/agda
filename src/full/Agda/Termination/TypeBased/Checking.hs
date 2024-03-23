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
import Debug.Trace
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
sizeCheckTerm :: SizeTele -> Term -> MonadSizeChecker SizeTele
sizeCheckTerm tp term' = do
  -- Turn projection-like function into a sequence of projections
  unProjectedTerm <- MSC $ elimView EvenLone term'
  term <- liftTCM $ tryReduceCopy unProjectedTerm
  -- now the term is ready for size processing
  sizeCheckTerm' tp term

-- | The same as @sizeCheckTerm@, but acts on a sufficiently normalized terms.
--   It is enough for the term to be free from Agda's internal sugar, such as projection-like functions or copied definitions.
sizeCheckTerm' :: SizeTele -> Term -> MonadSizeChecker SizeTele
sizeCheckTerm' expected t@(Var i elims) = do
  context <- getCurrentCoreContext
  case lookup i context of
    Nothing -> do
      reportSDoc "term.tbt" 20 $ vcat
        [ "Unknown variable" <+> prettyTCM t
        , "Where the context is" <+> text (show context)
        ]
      _ <- sizeCheckEliminations UndefinedSizeTele elims
      -- This branch is possible if the codomain of the processed function is large-eliminated.
      -- In this case, the pattern encoder can lose some variables.
      pure $ UndefinedSizeTele
    Just sizeTypeOfVar -> do
      -- We need to freshen generic arguments, because each usage of a polymorphic variable implies new parameterization
      freshenedSizeType <- freshenGenericArguments sizeTypeOfVar
      reportSDoc "term.tbt" 20 $ vcat
        [ "Inferring size type of var" <+> prettyTCM t
        , "Expected type             : " <+> text (show expected)
        , "Type of var (original)    : " <+> text (show sizeTypeOfVar)
        , "Type of var (fresh gen)   : " <+> text (show freshenedSizeType)
        , "Eliminations              : " <+> prettyTCM elims
        ]
      remainingCodomain <- sizeCheckEliminations sizeTypeOfVar elims
      inferenceToChecking expected remainingCodomain
      pure remainingCodomain
sizeCheckTerm' expected t@(Def qn elims) = if isAbsurdLambdaName qn then pure UndefinedSizeTele else do
  -- New size variables in a freshened definitions are those that were populated during the freshening. Yes, a bit of an abstraction leak, TODO
  currentSizeLimit <- MSC $ gets scsFreshVarCounter
  constInfo <- getConstInfo qn
  sizeSigOfDef <- resolveConstant qn
  case sizeSigOfDef of
    Nothing -> do
      reportSDoc "term.tbt" 20 $ "No size type for definition" <+> prettyTCM qn
      pure UndefinedSizeTele
    -- This definition is a function, which has no interesting size bounds, so we can safely ignore them
    Just (_, sizeTypeOfDef) -> do
      newSizeVariables <- MSC (gets scsFreshVarCounter) <&> \x -> [currentSizeLimit .. (x - 1)]
      let (_, scodomain) = sizeCodomain sizeTypeOfDef
      coreType <- MSC $ typeOfConst qn
      reportSDoc "term.tbt" 20 $ vcat $
        [ "Freshened definition" <+> prettyTCM qn <+> ":" ] ++ map (nest 2)
        [ "Term: " <+> prettyTCM t
        , "coreType: " <+> prettyTCM coreType
        , "elims: " <+> prettyTCM elims
        , "expected type: " <+> text (show expected)
        , "Freshened inferred type:" <+> text (show sizeTypeOfDef)
        , "is copy: " <+> text (show (defCopy constInfo))
        ]
      remainingCodomain <- sizeCheckEliminations sizeTypeOfDef elims

      -- We need to record the occurrence of a possible size matrix at this place.
      maybeStoreRecursiveCall qn elims newSizeVariables

      reportSDoc "term.tbt" 20 $ "Substituted codomain of" <+> prettyTCM qn  <+> ":" <+> text (show remainingCodomain)
      inferenceToChecking expected remainingCodomain

      pure remainingCodomain
sizeCheckTerm' expected t@(Con ch ci elims) = do
  let (stDomainLength, stCodomain) = sizeCodomain expected
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
  realType <- MSC $ typeOfConst constructorName
  reportSDoc "term.tbt" 20 $ vcat $
    [ "freshened constructor" <+> prettyTCM constructorName <+> ":"] ++ map (nest 2)
    [ "term: " <+> prettyTCM t
    , "elims: " <+> prettyTCM elims
    , "real type: " <+> prettyTCM realType
    , "expected type: " <+> text (show expected)
    , "substituted signature:" <+> text (show tele)
    ]

  -- Constructor type has a prepended telescope of enclosing module parameters and parameters of its datatype
  -- We need to apply this telescope to refine possible generics in the constructor type before actual elimination of constructor type.
  dataParameters <- liftTCM $ getDatatypeParametersByConstructor constructorName
  let initialConstructorArguments = case stCodomain of
        UndefinedSizeTele -> replicate dataParameters UndefinedSizeTele
        _ -> take dataParameters (unwrapSizeTree stCodomain)
  let preparedConstructorType = applyDataType initialConstructorArguments tele

  reportSDoc "term.tbt" 20 $ vcat $ map (nest 2)
    [ "constructor with applied data arguments:" <+> text (show preparedConstructorType)
    , "data parameters:" <+> text (show dataParameters)
    ]
  remainingCodomain <- sizeCheckEliminations preparedConstructorType elims
  inferenceToChecking expected remainingCodomain
  pure remainingCodomain
sizeCheckTerm' _ (Level _) = pure $ SizeTree SUndefined [] -- TODO
sizeCheckTerm' expected t@(Lam info tm) = do
  reportSDoc "term.tbt" 20 $ vcat
    [ "Dispatching into lambda"
    , "Expected size type: " <+> text (show expected)
    ]
  let (argSizeType, rest) = case expected of
        SizeArrow pt rest -> (pt, rest)
        StoredGeneric args i | args > 0 -> (UndefinedSizeTele, StoredGeneric (args - 1) i)
        SizeGeneric _ _ rest -> (SizeTree SUndefined [], rest)
        UndefinedSizeTele -> (UndefinedSizeTele, UndefinedSizeTele)
        _ -> __IMPOSSIBLE__
  let wrapWithGenericInst action = case expected of
        StoredGeneric args i | args > 0 -> do
          -- So we are processing a term of type `P : A -> B -> Set`
          -- We should not announce that we have found the instance of P, since someone may use it and get a wrong type.
          -- Forbidding instantiation here makes P instantiate to the outermost Pi-tower, which ensures that resulting generic has a correct arity.
          reportSDoc "term.tbt" 20 "Forbidding unification"
          result <- forbidGenericInstantiation i action
          unify args i result
          pure result
        _ -> action

  wrapWithGenericInst $ case tm of
    Abs arg tm -> do
      -- We still need to maintain internal context to get pretty-printed termination errors
      checkedTerm <- abstractCoreContext 0 argSizeType $ addContext arg $ sizeCheckTerm rest tm
      abstractSizeTele argSizeType checkedTerm
    NoAbs _ tm -> do
      checkedTerm <- sizeCheckTerm rest tm
      abstractSizeTele UndefinedSizeTele checkedTerm
sizeCheckTerm' (SizeGeneric args i rest) t@(Pi _ _) = do
  -- This branch is an application of some size type to a second-order size parameter.
  reportSDoc "term.tbt" 20 $ "Encoding generic pi-type:" <+> prettyTCM t

  encodedPi <- encodeTermMSC (El __UNREACHABLE__ t)

  -- let sigWithfreshenedSizes = instantiateSizeTele encodedPi newVars
  unify args i encodedPi
  return $ SizeTree SUndefined []
sizeCheckTerm' _ (Pi _ _) = pure UndefinedSizeTele
sizeCheckTerm' expected t@(MetaV _ el) = do
  inst <- MSC $ instantiate t
  case inst of
    MetaV _ _ -> pure $ SizeTree SUndefined []
    t -> sizeCheckTerm expected t
sizeCheckTerm' _ (Lit _) = pure UndefinedSizeTele -- todo
sizeCheckTerm' (StoredGeneric args i) (Sort _) = do
  unify args i UndefinedSizeTele
  pure UndefinedSizeTele
sizeCheckTerm' _ (Sort _) = pure UndefinedSizeTele
sizeCheckTerm' _ (DontCare _) = pure UndefinedSizeTele
sizeCheckTerm' _ (Dummy _ _) = pure UndefinedSizeTele

-- | Allows to convert an internal type to a size type within the @MonadSiseChecker@ monad
encodeTermMSC :: Type -> MonadSizeChecker SizeTele
encodeTermMSC t = do
  currentGenericCounter <- getCurrentGenericCounter
  ctx <- getCurrentCoreContext
  currentFlexCounter <- MSC $ gets scsFreshVarCounter
  encodingResult <- MSC $ liftTCM $ typeToSizeTele currentFlexCounter currentGenericCounter
    ([case lookup ind ctx of
      Just (StoredGeneric args i) -> Just i
      _ -> Nothing | ind <- [0..length ctx]]) (const False) t
  let newRegVars = erNewFirstOrderVariables encodingResult
  let newGenArities = erNewGenericArities encodingResult
  let encodedPi = erEncodedType encodingResult
  reportSDoc "term.tbt" 20 $ vcat
    [ "regVars: " <+> text (show newRegVars)
    , "genVarArities: " <+> text (show newGenArities)
    , "currentFlexCounter: " <+> text (show currentFlexCounter)
    , "currentGenericCounter: " <+> text (show currentGenericCounter)]
  newVars <- replicateM (newRegVars - currentFlexCounter) requestNewVariable
  newGens <- forM newGenArities requestNewGeneric
  pure $ encodedPi

maybeStoreRecursiveCall :: QName -> Elims  -> [Int] -> MonadSizeChecker ()
maybeStoreRecursiveCall qn elims callSizes = do
  names <- currentMutualNames
  tryReduceNonRecursiveClause qn elims names (\_ -> reportSDoc "term.tbt" 40 "Call is reduced away")
    (do
      currentSymbol <- currentCheckedName
      rootArity <- getRootArity
      let rootFunctionSizes =  [0..(rootArity - 1)]
      storeCall currentSymbol qn rootFunctionSizes callSizes elims
    )

-- | Records the constraints obtained from comparing inferred and checked size types.
-- This is more or less standard transition from checking to inference in bidirectional type checking.
inferenceToChecking :: SizeTele -> SizeTele -> MonadSizeChecker ()
inferenceToChecking expected inferred = case expected of
  StoredGeneric args i -> unify args i inferred
  t -> inferred `smallerOrEq` expected

datatypeArguments :: Int -> SizeTele -> Int
datatypeArguments fallback (SizeTree _ args) = length args
datatypeArguments fallback _ = fallback

-- | This size signature carries zero information. Effectively erases all information about the types.
isDumbType :: SizeTele -> Bool
isDumbType (SizeTree SUndefined []) = True
isDumbType _ = False


-- | We cannot do argument checking in a straightforward zip-loop, because an instantiation of a generic may unlock new possibility for elimination.
-- Example : `apply foo a b`, where `apply : (A -> B) -> A -> B` and `foo : C -> D -> E`. Here instantiation of `B` is `D -> E`, which unlocks the application of `b`.
-- Returns the residual codomain in the end of the list.
-- This is analogous to @checkSpine@ in the double checker.
sizeCheckEliminations :: SizeTele -> Elims -> MonadSizeChecker SizeTele
sizeCheckEliminations eliminated [] = pure eliminated
sizeCheckEliminations eliminated@UndefinedSizeTele (elim : elims) = do
  arg <- case elim of
    Apply (Arg _ t) -> sizeCheckTerm UndefinedSizeTele t
    _ -> pure UndefinedSizeTele
  sizeCheckEliminations eliminated elims
sizeCheckEliminations eliminated (elim : elims) = do
  reportSDoc "term.tbt" 80 $ "gradualElimsCheck" <+> vcat
    [ "full sizeType to eliminate: " <+> text (show eliminated)
    , "currently applied elimination: " <+> prettyTCM elim
    ]
  case (elim, eliminated) of
    (Proj _ qname, eliminatedRecord@(SizeTree root args)) -> do
      (inferredRecordType, projectionCodomain) <- eliminateProjection qname eliminatedRecord args
      sizeCheckEliminations projectionCodomain elims
    (Apply (Arg _ t), StoredGeneric args i) | args > 0 -> do
      _ <- sizeCheckTerm UndefinedSizeTele t
      -- We are starting to check arguments against a generic variable, where all new applications just increase the number of stored arguments for it.
      sizeCheckEliminations (SizeGenericVar 1 i) elims
    (Apply (Arg _ t), SizeGenericVar args i) -> do
      _ <- sizeCheckTerm UndefinedSizeTele t
      sizeCheckEliminations (SizeGenericVar (args + 1) i) elims
    (Apply (Arg _ t), SizeGeneric arity i rest) -> do
      checkedDomain <- case t of
        -- Unfortunately, we have to apply counter-measures for Set-valued functions and do reductions, since we work in System F,
        -- and the internal syntax is written in dependent types.
        -- If we don't do it, then typealiases will be invisible for our termination checker.
        -- I conjecture that all these reductions happen on type-level (well, most of them), so they should not slow down the system significantly.
        (Def qn _) -> do
          reportSDoc "term.tbt" 20 $ "Reduction in gradualElimsCheck of " <+> prettyTCM qn
          def <- getConstInfo qn
          TelV _ codomain <- MSC $ telView (defType def)
          term <- if (isJust . isSort . unEl $ codomain) && isTerminatingDefinition def
            then liftTCM . tryReduceCopy =<< MSC (reduce t)
            else pure t
          case term of
            Def qn _ -> do
              copy <- defCopy <$> getConstInfo qn
              reportSDoc "term.tbt" 20 $ "Is reduced definition copied:" <+> text (show copy)
            _ -> pure ()
          sizeCheckTerm (StoredGeneric arity i) term
        _ -> sizeCheckTerm (StoredGeneric arity i) t
      rest <- sizeInstantiate rest
      sizeCheckEliminations rest elims
    (Apply (Arg _ t), SizeArrow arg rest) -> do
      checkedDomain <- sizeCheckTerm arg t
      sizeCheckEliminations rest elims
    (Proj _ t, tele) -> trace ("projection " ++ show t ++ " over unsupported size type: " ++ show tele) __IMPOSSIBLE__
    (Apply (Arg _ t), _) -> do
      reportSDoc "term.tbt" 20 $ vcat
        [ "Elimination of unsupported size type:"
        , "elim: " <+> prettyTCM elim
        , "expected size type: " <+> text (show eliminated)
        ]
      __IMPOSSIBLE__
    (IApply _ _ _, _) -> trace "elimination of cubical thing, bad" __IMPOSSIBLE__

-- | Eliminates projection, returns inferred type of eliminated record and the residual inferred codomain of projection.
eliminateProjection :: QName -> SizeTele -> [SizeTele] -> MonadSizeChecker (SizeTele, SizeTele)
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
  reportSDoc "term.tbt" 40 $ vcat $ map (nest 2) $
    [ "Eliminating projection:" <+> prettyTCM projName
    , "of type: " <+> (text (show projectionType))
    , "with record carrier: " <+> (text (show eliminatedRecord))
    , "and constraints: " <+> (text (show constraints))
    ]
  let inferredProjectionType = applyDataType recordArgs projectionType
  reportSDoc "term.tbt" 40 $ "Applied projection type: " <+> text (show inferredProjectionType)
  case inferredProjectionType of
    SizeArrow inferredRecordDef restDef -> do
      -- The order here is a bit tricky.
      -- One may argue that `eliminatedRecord` comes from the position of expected type, which means that it should be "bigger" than its argument.
      -- However, in this case we are not _eliminating a record (datatype) with a projection (function)_,
      -- we are _eliminating a projection (function) with a record (argument to a function)_.
      -- It means that the inferred first parameter of projection actually becomes the expected type of the record.
      eliminatedRecord `smallerOrEq` inferredRecordDef
      pure (inferredRecordDef, restDef)
    UndefinedSizeTele -> pure (UndefinedSizeTele, UndefinedSizeTele)
    _ -> trace "elimination of non-arrow size type" __IMPOSSIBLE__

-- | Instantiates all generic variables in `SizeTele`
sizeInstantiate :: SizeTele -> MonadSizeChecker SizeTele
sizeInstantiate (SizeArrow l r) = SizeArrow <$> sizeInstantiate l <*> sizeInstantiate r
sizeInstantiate (SizeGeneric args i r) = SizeGeneric args i <$> sizeInstantiate r
sizeInstantiate (SizeTree sd tree) = SizeTree <$> pure sd <*> traverse sizeInstantiate tree
sizeInstantiate (SizeGenericVar args i) = do
  inst <- getGenericInstantiation i
  case inst of
    Nothing -> pure $ SizeGenericVar args i
    Just s@(StoredGeneric storedArgs i) -> trace ("Impossible stored generic instaniation in unification: " ++ show s) __IMPOSSIBLE__
    Just t -> pure $ applyDataType (replicate args UndefinedSizeTele) t

-- | @unify mainArgs i st@ performs unification of a generic index @i := st@, while tracking the arity of @i@
unify :: Int -> Int -> SizeTele -> MonadSizeChecker ()
unify mainArgs i st = ifM (MSC $ (IntSet.member i) <$> gets scsForbidUnification) (reportSDoc "term.tbt" 40 "Aborting unification because forbidden") $ do
  reportSDoc "term.tbt" 20 $ "Unification:" <+> (text (show $ StoredGeneric mainArgs i)) <+> " ==> " <+> text (show st)
  let actualSt = case st of
        StoredGeneric args i -> SizeGenericVar 0 i
        _ -> st
  recordInstantiation i actualSt


-- | Compares two size types and stores the obtained constraints.
--   The idea is that during the later computation of assignment for flexible types,
--   all these constraints should be respected.
smallerOrEq :: SizeTele -> SizeTele -> MonadSizeChecker ()
smallerOrEq (SizeTree s1 tree1) (SizeTree s2 tree2) = do
  ifM (isContravariant s1 `or2M` isContravariant s2) {- then -} (smallerSize s2 s1) {- else -} (smallerSize s1 s2)
  zipWithM_ smallerOrEq tree1 tree2
  where
    smallerSize :: Size -> Size -> MonadSizeChecker ()
    smallerSize (SDefined i1) (SDefined i2) = do
      reportSDoc "term.tbt" 20 $ "Registering:" <+> text (show i1) <+> "<=" <+> text (show i2)
      storeConstraint (SConstraint SLeq i1 i2)
    smallerSize SUndefined (SDefined i) = markUndefinedSize i
    smallerSize _ _ = pure ()
smallerOrEq (UndefinedSizeTele) _ = pure ()
smallerOrEq _ (UndefinedSizeTele) = pure ()
smallerOrEq t1@(SizeGenericVar args1 i1) t2@(SizeGenericVar args2 i2) =
  when (i1 == i2 && args1 /= args2) $ do
    reportSDoc "term.tbt" 20 $ vcat
      ["Attempt to compare incomparable generic variables:"
      , "t1: " <+> text (show t1)
      , "t2: " <+> text (show t2)
      ]
    __IMPOSSIBLE__
smallerOrEq (SizeArrow d1 c1) (SizeArrow d2 c2) = d2 `smallerOrEq` d1 >> c1 `smallerOrEq` c2 -- note the contravariance in domain
smallerOrEq (SizeGeneric _ _ _) _ = pure ()
smallerOrEq _ (SizeGeneric _ _ _) = pure ()
smallerOrEq (SizeTree _ _) (SizeArrow _ _) = pure () -- can occur, becase encoding of terms is intentionaly not complete
smallerOrEq (SizeArrow _ _) (SizeTree _ _) = pure ()
smallerOrEq (SizeArrow _ r) (SizeGenericVar args i) = r `smallerOrEq` (SizeGenericVar (args + 1) i) -- eta-conversion
smallerOrEq (SizeGenericVar args i) (SizeArrow _ r) = (SizeGenericVar (args + 1) i) `smallerOrEq` r -- eta-conversion
smallerOrEq t1 t2 = do
  -- One example of a problem is an attempt to compare generic var and size variable.
  -- This is an internal error, because it means that there is a forgotten instantiation somewhere.
  reportSDoc "term.tbt" 20 $ vcat
    ["Attempt to compare incomparable terms:"
    , "t1: " <+> text (show t1)
    , "t2: " <+> text (show t2)
    ]
  __IMPOSSIBLE__


-- | Retrieves sized type for a constant
-- May return Nothing for primitive definition
resolveConstant :: QName -> MonadSizeChecker (Maybe ([SConstraint], SizeTele))
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
  reportSDoc "term.tbt" 40 $ vcat
    [ "Left stored name: " <+> prettyTCM q1
    , "Right stored name: " <+> prettyTCM q2
    , "left vars:  " <+> text (show sizesq1)
    , "right vars: " <+> text (show sizesq2)
    ]
  when (q1 `Set.member` names && q2 `Set.member` names) do
    doc <- buildRecCallLocation q2 elims
    reportCall q1 q2 sizesq1 sizesq2 doc
    when (q1 == q2) $ do
      forM_ (zip sizesq2 sizesq1) (uncurry addFallbackInstantiation)
      reportDirectRecursion sizesq2

unwrapSizeTree :: SizeTele -> [SizeTele]
unwrapSizeTree (SizeTree _ ts) = ts
unwrapSizeTree t = trace ("t: " ++ show t) __IMPOSSIBLE__

isTerminatingDefinition :: Definition -> Bool
isTerminatingDefinition d = case theDef d of
  Function{ funTerminates } | funTerminates == Just True -> True
  _ -> False

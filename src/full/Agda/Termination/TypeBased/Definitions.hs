{- | This module is a control center of type-based termination,
     which orchestrates different parst of type-based termination
-}
module Agda.Termination.TypeBased.Definitions where

import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
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
import Control.Monad.Trans
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Telescope
import Agda.Termination.TypeBased.Common
import Agda.Termination.TypeBased.Preservation
import Agda.Termination.TypeBased.Patterns
import Agda.TypeChecking.Substitute
import Agda.Termination.TypeBased.Monad
import Agda.TypeChecking.ProjectionLike
import Agda.Utils.Impossible
import Agda.Termination.TypeBased.Checking
import Control.Monad
import Agda.TypeChecking.Pretty
import Debug.Trace
import Agda.Utils.Monad
import Agda.Termination.Common
import Data.Maybe
import Agda.Termination.TypeBased.Encoding
import Agda.Termination.CallGraph
import Agda.Termination.Monad
import Agda.Termination.TypeBased.Graph
import Data.Foldable (traverse_)
import Agda.Utils.List ((!!!))
import Data.Functor ((<&>))
import Agda.Termination.CallMatrix
import qualified Agda.Termination.CallMatrix
import Agda.Utils.Graph.AdjacencyMap.Unidirectional (Edge(..))
import Data.Either
import Agda.Utils.Singleton
import Agda.Termination.Order (Order)
import qualified Agda.Termination.Order as Order


-- | 'initSizeTypeEncoding names' computes size types for every definition in 'names'
-- It is expected that 'names' form a mutual block.
initSizeTypeEncoding :: Set QName -> TCM ()
initSizeTypeEncoding mutuals = forM_ mutuals $ \nm -> inConcreteOrAbstractMode nm $ \def -> do
  -- Unless there is an explicit command, we will not do non-trivial encoding
  encodeComplex <- typeBasedTerminationOption
  let dType = defType def
  sizedSignature <- case theDef def of
    Datatype { dataCons, dataMutual } -> do
      reportSDoc "term.tbt" 20 $ vcat
        [ "Starting encoding for data: " <+> prettyTCM nm
        , "  with mutual block: " <+> prettyTCM (Set.toList mutuals)
        , "  of core type:" <+> prettyTCM dType
        ]
      sizedSignature <- encodeDataType dataCons mutuals encodeComplex False dType
      reportSDoc "term.tbt" 20 $ "Encoded data" <+> prettyTCM nm <+> ", sized type: " <+> text (show sizedSignature)
      pure $ Just sizedSignature
    Record { recConHead, recInduction } -> do
      reportSDoc "term.tbt" 20 $ vcat
        [ "Starting encoding for record:" <+> prettyTCM nm
        , "  of core type:" <+> prettyTCM dType
        ]
      sizedSignature <- encodeDataType [conName recConHead] mutuals encodeComplex (recInduction == Just CoInductive) dType
      reportSDoc "term.tbt" 20 $ "Encoded record" <+> prettyTCM nm <+> ", sized type:" <+> text (show sizedSignature)
      pure $ Just sizedSignature
    Constructor{ conData } -> do
      reportSDoc "term.tbt" 20 $ vcat
        [ "Starting encoding for constructor:" <+> prettyTCM nm
        , "  with mutual block: " <+> prettyTCM (Set.toList mutuals)
        , "  of core type:" <+> prettyTCM dType
        , "  of data type:" <+> prettyTCM conData
        ]
      sizedSignature <- lowerIndices <$> if encodeComplex then encodeConstructorType mutuals dType else pure $ encodeBlackHole dType
      reportSDoc "term.tbt" 20 $ "Encoded constructor" <+> prettyTCM nm <+> ", sized type:" <+> text (show sizedSignature) <+> "encoded complex: " <+> text (show encodeComplex)
      pure $ Just sizedSignature
    Function { funProjection } -> do
      reportSDoc "term.tbt" 20 $ vcat
        [ "Starting encoding for function:" <+> prettyTCM nm
        , "  of core type:" <+> prettyTCM dType
        ]
      sizedSignature <- lowerIndices <$> if encodeComplex
        then case funProjection of
          Left  _ -> encodeFunctionType dType
          Right _ -> encodeFieldType mutuals dType
        else pure $ encodeBlackHole dType
      reportSDoc "term.tbt" 20 $ "Encoded function" <+> prettyTCM nm <+> ", sized type:" <+> text (show sizedSignature)
      pure $ Just sizedSignature
    Axiom {} -> do
      reportSDoc "term.tbt" 20 $ vcat
        [ "Starting encoding for axiom:" <+> prettyTCM nm
        , "  of core type:" <+> prettyTCM dType
        ]
      sizedSignature <- if encodeComplex then encodeFunctionType dType else pure $ encodeBlackHole dType
      reportSDoc "term.tbt" 20 $ "Encoded axiom" <+> prettyTCM nm <+> ", sized type:" <+> text (show sizedSignature)
      pure $ Just sizedSignature
    _ -> return Nothing
  case sizedSignature of
    Just x -> addConstant nm $ def { defSizedType = Just x }
    Nothing -> return ()


-- | An entry point for checking a mutual block for type-based termination.
--   This function returns a set of size-change termination matrices or an error.
--   It also has a side effect of computing size preservation for a block.
collectTerminationData :: Set QName -> TCM (Either [String] (CallGraph CallPath))
collectTerminationData names = do
  -- Termination checking makes sense only for functions, since this is the definition that can call itself.
  functions <- mapMaybeM (\n -> inConcreteOrAbstractMode n $ \def -> do
    case theDef def of
      FunctionDefn funData -> pure $ Just (funData, n)
      _ -> pure Nothing) (Set.toList names)
  result <- forM functions (uncurry $ processSizedDefinition names)
  let (errors, terminationResult) = partitionEithers result
  case errors of
    [] -> do
      -- Signatures may be changed after termination checking because of size preservation
      -- So we will store them here.
      forM_ terminationResult $ \(qn, _, sig) -> inConcreteOrAbstractMode qn $ \def -> do
        addConstant qn (def { defSizedType = Just sig })
      let totalCalls = mconcat (map (\(_,a,_) -> a) terminationResult)
      pure $ Right totalCalls
    _ ->
      -- If there is an error happened during termination checking, it makes no sense to process matrices.
      pure $ Left $ mconcat errors


-- | Launches type-based termination processing on a given definition.
processSizedDefinition :: Set QName -> FunctionData -> QName -> TCM (Either [String] (QName, CallGraph CallPath, SizeSignature))
processSizedDefinition names funData nm = inConcreteOrAbstractMode nm $ \d -> do
  def <- getConstInfo nm
  let clauses = _funClauses funData
  reportSDoc "term.tbt" 20 $ "Hello function:" <+> prettyTCM nm <+> " (copy:" <+> text (show $ defCopy def) <+> ")"
  reportSDoc "term.tbt" 20 $ "Function type: " <+> (prettyTCM =<< typeOfConst nm)
  -- Since we are processing this function, it was certainly encoded.
  let s = fromJust (defSizedType def)
  res <- invokeSizeChecker nm names (processSizedDefinitionMSC s clauses)
  case res of
    Left err -> pure $ Left err
    Right (callGraph, sig) -> do
      reportSDoc "term.tbt" 20 $ vcat
        [ "Call graph from inferred sizes: "
        , pretty callGraph
        ]
      return $ Right (nm, callGraph, sig)


processSizedDefinitionMSC :: SizeSignature -> [Clause] -> MonadSizeChecker (IntMap SizeExpression, SizeSignature)
processSizedDefinitionMSC s@(SizeSignature bounds contra sizeSig) clauses = do
  (_, newTele) <- freshenSignature s
  initSizePreservationStructure newTele

  localSubstitutions <- forM clauses (processSizeClause bounds newTele)

  -- This is in fact a disjoint union, since all variables are different for each clause.
  let combinedSubst = IntMap.unions localSubstitutions
  amendedSubst <- considerIncoherences combinedSubst
  let (domains, _) = sizeCodomain sizeSig

  fixedSignature <- if domains > 0 then applySizePreservation s else pure s

  pure $ (amendedSubst, fixedSignature)

  where

    -- Assigns all incoherent rigid variables to infinity, since they cannot be used for termination analysis adequately.
    considerIncoherences :: IntMap SizeExpression -> MonadSizeChecker (IntMap SizeExpression)
    considerIncoherences combinedSubst = do
      totalGraph <- MSC $ gets scsConstraints
      currentName <- currentCheckedName
      arity <- getArity currentName
      incoherences <- liftTCM $ collectIncoherentRigids combinedSubst (concat totalGraph)
      reportSDoc "term.tbt" 40 $ "Incoherent sizes: " <+> text (show incoherences)
      let baseSize = SEMeet (replicate arity (-1))
      pure $ IntMap.mapWithKey (\i expectedSize@(SEMeet list) -> if (any (`IntSet.member` incoherences) list) then baseSize else expectedSize) combinedSubst


-- | Given a clause, builds an assignment for all size variables occurred in this clause
processSizeClause :: [SizeBound] -> SizeTele -> Clause -> MonadSizeChecker (IntMap SizeExpression)
processSizeClause bounds newTele c = do
  initNewClause bounds
  if (hasDefP (namedClausePats c))
  then pure IntMap.empty
  else do
    expectedTele <- encodeFunctionClause newTele c
    reportSDoc "term.tbt" 20 $ "Clause to be processed: " <+> prettyTCM c

    ifM (null <$> MSC (gets scsErrorMessages)) (
        case clauseBody c of
        Just body -> do
            addContext (clauseTel c) $ sizeCheckTerm expectedTele body >> pure ()
        _ -> do
            reportSDoc "term.tbt" 20 $ "Aborting processing of clause, because there is no body"
            return ()
        ) (do
        reportSDoc "term.tbt" 20 $ "Aborting processing of clause, because error during encoding happened"
        return ())
    newConstraints <- getCurrentConstraints
    refinePreservedVariables
    reportSDoc "term.tbt" 20 $ vcat $ ("Clause size constraints:") : (map (nest 2 . text . show) newConstraints)
    rigids <- getCurrentRigids
    simplifySizeGraph True rigids newConstraints


invokeSizeChecker :: QName -> Set QName -> MonadSizeChecker (IntMap SizeExpression, SizeSignature) -> TCM (Either [String] (CallGraph CallPath, SizeSignature))
invokeSizeChecker rootName nms action = do
  ((subst, sizePreservationInferenceResult), res) <- runSizeChecker rootName nms action
  let graph = scsConstraints res
  let calls = scsRecCalls res
  reportSDoc "term.tbt" 20 $ vcat $
    [ text "Raw graph:" ] ++
    map (nest 2 . text . show) graph ++
    [ "Final substitution: "] ++
    map (nest 2 . text ) (map (\i -> (show (SDefined i)) ++ " ↦ " ++ show (subst IntMap.! i)) (IntMap.keys subst)) ++
    [ "Calls: " ] ++
    map (nest 2 . text . show) calls
  let indexing = zip (Set.toList nms) [0..]

  case scsErrorMessages res of
    [] -> do
      -- No internal errors, let's proceed with building size-change matrices
      edges <- forM calls (\(q1, q2, sizes1, sizes2, place) -> do
            let matrix = makeCM (length sizes1) (length sizes2) (List.transpose $ composeMatrix subst sizes1 sizes2)
                n = fromJust $ List.lookup q1 indexing
                m = fromJust $ List.lookup q2 indexing
            reportSDoc "term.tbt" 20 $ "Matrix between" <+> prettyTCM q1 <+> "and" <+> prettyTCM q2 <+> text ("(" ++ show sizes2 ++ ")") <+> "is" <+> pretty matrix
            pure $ Edge n m $ singleton $ CallMatrixAug matrix $ CallPath $ fromList [CallInfo q2 place])
      pure $ Right (fromList edges, sizePreservationInferenceResult)
    l -> pure $ Left l

-- | Populates a set of rigid variables and internal context according to the LHS of a clause.
--   Returns the expected type of a clause, which may be different from semi-applied function type because of copatterns
encodeFunctionClause :: SizeTele -> Clause -> MonadSizeChecker SizeTele
encodeFunctionClause sizeTele c = do
  let patterns = namedClausePats c
  reportSDoc "term.tbt" 20 $ vcat
    [ "starting encoding of clause: " <+> prettyTCM c
    , "with domains: " <+> text (show sizeTele)
    ]
  (leafVariables, tele) <- matchPatterns sizeTele patterns
  setLeafSizeVariables leafVariables
  patternContext <- getCurrentCoreContext
  sizeContext <- getCurrentRigids
  contra <- getContravariantSizeVariables
  reportSDoc "term.tbt" 20 $ vcat
    [ "finished encoding of clause: " <+> prettyTCM c
    , "var context :            " <+> text (show patternContext)
    , "size context:            " <+> text (show sizeContext)
    , "contravariant variables: " <+> text (show contra)
    , "leaf variables:          " <+> text (show leafVariables)
    , "expected type of clause: " <+> text (show tele)
    ]
  return tele


encodeDataType :: [QName] -> Set QName -> Bool -> Bool -> Type -> TCM SizeSignature
encodeDataType ctors fullSet generify isCoinductiveRecord tp = do
  let TelV domains codomain = telView' tp
  -- We need to check if a datatype is actually recursive
  -- This helps a lot for performance, since it allows us to not introduce a lot of superfluous size variables,
  -- which in turn makes the graph solving faster.
  isRecursiveData <- anyM ctors (checkRecursiveConstructor fullSet)

  pure $ SizeSignature
         (if isRecursiveData then [SizeUnbounded] else [])
         (if isCoinductiveRecord && isRecursiveData then [0] else [])
         (encodeDatatypeDomain isRecursiveData 0 generify [] domains)

-- | 'checkRecursiveConstructor allNames qn' checks that a construtor with the name 'qn' refers to any of the 'allNames',
-- thus giving us the information if this constructor is recursive.
--
-- In fact, this is a job of the positivity checker.
-- We cannot use the actual positivity checker because it runs too late.
-- It makes sense: the positivity checker unfolds definitions, and for that it needs to know that the unfolding is safe, i.e. the definition is terminating.
-- However, we need to know recursivity of definitions _for_ termination checking, which means that we should design some ad-hoc solution.
checkRecursiveConstructor :: Set QName -> QName -> TCM Bool
checkRecursiveConstructor allNames qn = do
  conType <- defType <$> getConstInfo qn
  (TelV dom _) <- telView conType
  findMention allNames dom
  where
    findMention :: Set QName -> Tele (Dom Type) -> TCM Bool
    findMention allNames EmptyTel = pure False
    findMention allNames (ExtendTel dt rest) = findMentionInTerm allNames (unEl (unDom dt)) `or2M` findMention allNames (unAbs rest)

    findMentionInTerm :: Set QName -> Term -> TCM Bool
    findMentionInTerm allNames (Def qn elims) = pure (qn `Set.member` allNames) `or2M` findMentionInElims allNames elims
    findMentionInTerm allNames (Pi dom cod) = (findMentionInTerm allNames (unEl (unDom dom))) `or2M` (findMentionInTerm allNames (unEl (unAbs cod)))
    findMentionInTerm allNames (Lam _ cod) = findMentionInTerm allNames (unAbs cod)
    findMentionInTerm allNames (Sort _) = pure False
    findMentionInTerm allNames (Var _ elims) = findMentionInElims allNames elims
    findMentionInTerm allNames (MetaV _ _) = pure False
    findMentionInTerm allNames (Level _) = pure False
    findMentionInTerm allNames (Lit _) = pure False
    findMentionInTerm allNames (DontCare _) = pure False
    findMentionInTerm allNames (Con _ _ elims) = findMentionInElims allNames elims
    findMentionInTerm allNames (Dummy _ _) = pure False

    findMentionInElims :: Set QName -> Elims -> TCM Bool
    findMentionInElims allNames elims = (anyM elims (\case
      Apply arg -> findMentionInTerm allNames $ unArg arg
      _ -> pure False))

-- | Converts the telescope of a datatype to a size type.
encodeDatatypeDomain :: Bool -> Int -> Bool -> [SizeTele] -> Tele (Dom Type) -> SizeTele
encodeDatatypeDomain isRecursive x _ params EmptyTel =
  let size = if isRecursive then SDefined 0 else SUndefined
  in SizeTree size params
encodeDatatypeDomain isRecursive ind generify params (ExtendTel dt rest) =
  let d = unEl $ unDom dt
      genericArity = inferGenericArity d
      (wrapper, ind', newParam) = if generify
        then case genericArity of
          Just arity -> (SizeGeneric arity ind, ind + 1, SizeGenericVar 0 ind)
          Nothing -> (SizeArrow UndefinedSizeTele, ind, UndefinedSizeTele)
        else (SizeArrow UndefinedSizeTele, ind, UndefinedSizeTele)
      tails = encodeDatatypeDomain isRecursive ind' generify (params ++ [newParam]) (unAbs rest)
  in wrapper tails
  where
    inferGenericArity :: Term -> Maybe Int
    inferGenericArity (Sort _) = Just 0
    inferGenericArity (Pi _ rest) = fmap (+ 1) (inferGenericArity $ unEl $ unAbs rest)
    inferGenericArity _ = Nothing


composeMatrix :: IntMap SizeExpression -> [Int] -> [Int] -> [[Order]]
composeMatrix subst ls rs = [ [ obtainOrder l (subst IntMap.!? r) | r <- rs ] | l <- ls ]

obtainOrder :: Int -> Maybe SizeExpression -> Order
obtainOrder  i Nothing = Order.unknown
obtainOrder  i (Just (SEMeet list))
  | i >= length list    = Order.unknown
  | list List.!! i == i = Order.le
  | list List.!! i > 0  = Order.lt
  | otherwise           = Order.unknown

{- | This module is a control center of type-based termination,
     which orchestrates different parst of type-based termination
-}
module Agda.Termination.TypeBased.Definitions
  ( initSizeTypeEncoding
  , collectTerminationData
  ) where

import Control.Monad ( forM_, forM )
import Data.Either ( partitionEithers )
import qualified Data.IntMap as IntMap
import Data.IntMap ( IntMap )
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.Maybe ( fromJust, isJust )
import qualified Data.Set as Set
import Data.Set ( Set )

import qualified Agda.Benchmarking as Benchmark
import Agda.Utils.Benchmark ( billTo )
import Agda.Syntax.Common ( Induction(CoInductive), Arg(unArg) )
import Agda.Syntax.Internal ( QName, Elim'(Apply), Clause(namedClausePats, clauseBody, clauseTel), Tele(..), Type, Type''(unEl), Abs(unAbs), Elims, Term(..), ConHead(conName), Dom, Dom'(unDom), arity )
import Agda.Syntax.Internal.Pattern ( hasDefP )
import Agda.Termination.CallGraph ( fromList, CallGraph )
import Agda.Termination.CallMatrix ( CallMatrixAug(CallMatrixAug) )
import Agda.Termination.Common ( makeCM )
import Agda.Termination.Monad ( CallPath(..) )
import Agda.Termination.TypeBased.Checking ( sizeCheckTerm )
import Agda.Termination.TypeBased.Common ( fixGaps, computeDecomposition, SizeDecomposition(..) )
import Agda.Termination.TypeBased.Encoding ( encodeFunctionType, encodeFieldType, encodeBlackHole, encodeConstructorType )
import Agda.Termination.TypeBased.Graph ( SizeExpression(..), simplifySizeGraph, collectIncoherentRigids, SizeSubstitution )
import Agda.Termination.TypeBased.Monad ( getCurrentConstraints, getTotalConstraints, getCurrentRigids, getCurrentCoreContext, initNewClause, setLeafSizeVariables, currentCheckedName,
      getRootArity, freshenSignature, runSizeChecker, TBTM, initSizePreservation, hasEncodingErrors, getBottomVariables, getInfiniteSizes, MutualRecursiveCall(..) )
import Agda.Termination.TypeBased.Preservation ( VariableInstantiation(ToInfinity), refinePreservedVariables, applySizePreservation, reifySignature )
import Agda.Termination.TypeBased.Patterns ( matchPatterns )
import Agda.Termination.TypeBased.Syntax ( SizeSignature(SizeSignature), SizeBound(SizeUnbounded), SizeType(..), Size(SUndefined, SDefined), pattern UndefinedSizeType )
import qualified Agda.Termination.Order as Order
import Agda.Termination.Order (Order)
import Agda.TypeChecking.Monad.Base ( TCM, Definition(defType, defPolarity, defCopy, theDef, defSizedType), MonadTCM(liftTCM), CallInfo(CallInfo), FunctionData(_funClauses),
      Defn(FunctionDefn), pattern Constructor, conData, pattern Record, recConHead, recInduction, pattern Datatype, dataCons, dataMutual, pattern Function, funProjection,
      pattern Axiom, typeBasedTerminationOption, sizePreservationOption )
import Agda.TypeChecking.Monad.Context ( AddContext(addContext) )
import Agda.TypeChecking.Monad.Debug ( reportSDoc )
import Agda.TypeChecking.Monad.Signature ( HasConstInfo(getConstInfo), addConstant, inConcreteOrAbstractMode, isProjection_ )
import Agda.TypeChecking.Pretty ( PrettyTCM(prettyTCM), pretty, nest, (<+>), vcat, text )
import Agda.TypeChecking.Polarity.Base ( Polarity(Covariant) )
import Agda.TypeChecking.Substitute ( TelV(TelV), telView' )
import Agda.TypeChecking.Telescope ( telView )
import Agda.Utils.Graph.AdjacencyMap.Unidirectional (Edge(..))
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Monad ( whenM, ifM, or2M, anyM, mapMaybeM )
import Agda.Utils.Singleton ( Singleton(singleton) )

-- | 'initSizeTypeEncoding names' encodes size types for every definition type in 'names'
-- It is expected that 'names' form a mutual block.
initSizeTypeEncoding :: Set QName -> TCM ()
initSizeTypeEncoding mutuals =
  billTo [Benchmark.TypeBasedTermination, Benchmark.SizeTypeEncoding] $ do
    forM_ mutuals $ \nm -> inConcreteOrAbstractMode nm $ \def -> do
      -- Unless there is an explicit command, we will not do non-trivial encoding
      encodeComplex <- typeBasedTerminationOption
      let dType = defType def
      sizedSignature <- case theDef def of
        Datatype { dataCons, dataMutual } -> do
          reportSDoc "term.tbt" 10 $ vcat
            [ "Starting encoding for data: " <+> prettyTCM nm
            , "  with mutual block: " <+> prettyTCM (Set.toList mutuals)
            , "  of internal type:" <+> prettyTCM dType
            ]
          sizedSignature <- encodeDataType dataCons mutuals encodeComplex False (defPolarity def) dType
          reportSDoc "term.tbt" 5 $ vcat
            [ "Encoded data " <> prettyTCM nm <> ", sized type: "
            , nest 2 $ pretty sizedSignature
            ]
          pure $ Just sizedSignature
        Record { recConHead, recInduction } -> do
          reportSDoc "term.tbt" 10 $ vcat
            [ "Starting encoding for record:" <+> prettyTCM nm
            , "  with mutual block: " <+> prettyTCM (Set.toList mutuals)
            , "  of internal type:" <+> prettyTCM dType
            ]
          sizedSignature <- encodeDataType [conName recConHead] mutuals encodeComplex (recInduction == Just CoInductive) (defPolarity def) dType
          reportSDoc "term.tbt" 5 $ vcat
            [ "Encoded record " <> prettyTCM nm <> ", sized type: "
            , nest 2 $ pretty sizedSignature
            ]
          pure $ Just sizedSignature
        Constructor{ conData } -> do
          reportSDoc "term.tbt" 10 $ vcat
            [ "Starting encoding for constructor:" <+> prettyTCM nm
            , "  with mutual block: " <+> prettyTCM (Set.toList mutuals)
            , "  of core type:" <+> prettyTCM dType
            ]
          sizedSignature <- fixGaps <$> if encodeComplex then encodeConstructorType mutuals dType else pure $ encodeBlackHole dType
          reportSDoc "term.tbt" 5 $ vcat
            [ "Encoded constructor " <> prettyTCM nm <> ", sized type: "
            , nest 2 $ pretty sizedSignature
            ]
          reportSDoc "term.tbt" 20 $ nest 2 $ "encoded complex: " <+> pretty encodeComplex
          pure $ Just sizedSignature
        Function { funProjection } -> do
          reportSDoc "term.tbt" 10 $ vcat
            [ "Starting encoding for function:" <+> prettyTCM nm
            , "  of core type:"
            , nest 2 $ prettyTCM dType
            ]
          sizedSignature <- fixGaps <$> if encodeComplex
            then case funProjection of
              Left  _ -> do
                sig@(SizeSignature _ contra tp) <- encodeFunctionType dType
                -- All positive occurrences of size variables should be infinity by default,
                -- as we do not know how the function behaves.
                let preservationCandidates = computeDecomposition (IntSet.fromList contra) tp
                reportSDoc "term.tbt" 50 $ vcat
                  [ "Preservation candidates: " <+> text (show preservationCandidates)
                  , "original sig:" <+> pretty sig
                  ]
                pure (reifySignature (List.sortOn fst (map (, ToInfinity) (sdPositive preservationCandidates ++ sdOther preservationCandidates))) sig)
              Right _ -> encodeFieldType mutuals dType
            else pure $ encodeBlackHole dType
          reportSDoc "term.tbt" 5 $ vcat
            [ "Encoded function " <> prettyTCM nm <> ", sized type:"
            , nest 2 $ pretty sizedSignature
            ]
          pure $ Just sizedSignature
        Axiom {} -> do
          reportSDoc "term.tbt" 10 $ vcat
            [ "Starting encoding for axiom:" <+> prettyTCM nm
            , "  of core type:"
            , nest 2 $ prettyTCM dType
            ]
          sizedSignature <- if encodeComplex then encodeFunctionType dType else pure $ encodeBlackHole dType
          reportSDoc "term.tbt" 5 $ vcat
            [ "Encoded axiom" <> prettyTCM nm <> ", sized type:"
            , nest 2 $ pretty sizedSignature
            ]
          pure $ Just sizedSignature
        _ -> return Nothing
      case sizedSignature of
        Just x -> addConstant nm $ def { defSizedType = x }
        Nothing -> return ()


-- | An entry point for checking a mutual block for type-based termination.
--   This function returns a set of size-change termination matrices or an error.
--   It also has a side effect of computing size preservation for a block.
collectTerminationData :: Set QName -> TCM (Either [String] (CallGraph CallPath))
collectTerminationData names = do
  -- Termination checking makes sense only for functions, since this is the definition that can call itself.
  functions <- mapMaybeM (\n -> inConcreteOrAbstractMode n $ \def -> do
    case theDef def of
      FunctionDefn funData | not (defCopy def || isJust (isProjection_ (theDef def))) -> pure $ Just (funData, n)
      _ -> pure Nothing) (Set.toList names)
  result <- forM functions (uncurry $ processSizedDefinition names)
  let (errors, terminationResult) = partitionEithers result
  case errors of
    [] -> do
      -- Signatures may be changed after termination checking because of size preservation
      -- So we will store them here.
      forM_ terminationResult $ \(qn, _, sig) -> inConcreteOrAbstractMode qn $ \def -> do
        addConstant qn (def { defSizedType = sig })
      let totalCalls = mconcat (map (\(_,a,_) -> a) terminationResult)
      pure $ Right totalCalls
    _ ->
      -- If there is an error happened during termination checking, it makes no sense to process matrices.
      pure $ Left $ mconcat errors


-- | Launches type-based termination processing on a given definition.
processSizedDefinition :: Set QName -> FunctionData -> QName -> TCM (Either [String] (QName, CallGraph CallPath, SizeSignature))
processSizedDefinition names funData nm = inConcreteOrAbstractMode nm $ \d -> do
  def <- defSizedType <$> getConstInfo nm
  let clauses = _funClauses funData
  reportSDoc "term.tbt" 10 $ "Starting type-based termination checking of the function:" <+> prettyTCM nm
  -- Since we are processing this function, it was certainly encoded.
  res <- invokeSizeChecker nm names (processSizedDefinitionTBTM clauses)
  case res of
    Left err -> pure $ Left err
    Right (callGraph, sig) -> do
      reportSDoc "term.tbt" 60 $ vcat
        [ "Joint call graph from type-based termination: "
        , pretty callGraph
        ]
      return $ Right (nm, callGraph, sig)

-- | Given a fully set environment (within @TBTM@), a definition is isomorphic to its set of clauses.
-- This function processes all definition's clauses, gathering a size substitution and a size signature after size preservation process.
processSizedDefinitionTBTM :: [Clause] -> TBTM (SizeSubstitution, SizeSignature)
processSizedDefinitionTBTM clauses = do
  qn <- currentCheckedName
  funType <- defType <$> getConstInfo qn
  sig@(SizeSignature bounds contra sizeType) <- liftTCM $ encodeFunctionType funType
  let decomposition = computeDecomposition (IntSet.fromList contra) sizeType
  initSizePreservation (sdNegative decomposition) (sdPositive decomposition)
  (_, newTele) <- freshenSignature Covariant sig

  localSubstitutions <- forM clauses $ processSizeClause bounds newTele

  -- This is in fact a disjoint union, since all variables are different for each clause.
  let combinedSubst = IntMap.unions localSubstitutions
  amendedSubst <- considerIncoherences combinedSubst

  fixedSignature <- billTo [Benchmark.TypeBasedTermination, Benchmark.Preservation] $ applySizePreservation sig

  pure $ (amendedSubst, fixedSignature)

  where

    -- Assigns all incoherent rigid variables to infinity, since they cannot be used for termination analysis adequately.
    considerIncoherences :: IntMap SizeExpression -> TBTM (IntMap SizeExpression)
    considerIncoherences combinedSubst = do
      totalGraph <- getTotalConstraints
      currentName <- currentCheckedName
      arity <- getRootArity
      incoherences <- liftTCM $ collectIncoherentRigids combinedSubst totalGraph
      reportSDoc "term.tbt" 60 $ "Incoherent sizes: " <+> text (show incoherences)
      let baseSize = SEMeet (replicate arity (-1))
      pure $ IntMap.mapWithKey (\i expectedSize@(SEMeet list) -> if (any (`IntSet.member` incoherences) list) then baseSize else expectedSize) combinedSubst


-- | Given a clause, builds a substitution for all size variables occurred in this clause
processSizeClause :: [SizeBound] -> SizeType -> Clause -> TBTM SizeSubstitution
processSizeClause bounds newTele c = do
  initNewClause bounds
  if (hasDefP (namedClausePats c))
  then pure IntMap.empty
  else do
    expectedTele <- billTo [Benchmark.TypeBasedTermination, Benchmark.PatternRigids] $ encodeFunctionClause newTele c
    reportSDoc "term.tbt" 10 $ "Starting checking the clause: " <+> prettyTCM c

    ifM hasEncodingErrors
     {- then -} (do
        reportSDoc "term.tbt" 70 $ "Aborting processing of clause, because error during encoding happened"
        return ())
     {- else -} (case clauseBody c of
        Just body -> billTo [Benchmark.TypeBasedTermination, Benchmark.SizeTypeChecking] $ do
            addContext (clauseTel c) $ sizeCheckTerm expectedTele body >> pure ()
        _ -> do
            reportSDoc "term.tbt" 70 $ "Aborting processing of clause, because there is no body"
            return ())
    newConstraints <- getCurrentConstraints

    -- Size preservation is a very expensive computation.
    -- Graph processing on its own is not cheap, as there may be up to 100.000 size variables in a single function (thanks to beta-normalized internal terms, this is achievable even without tactics).
    -- Luckily, we use a quasilinear algorithm for graphs of size variables.
    -- But then, size preservation can make the algorithm run thousands of times, and in that case even quasi-linearity does not save us.
    -- TODO: need better size-preservation analysis.
    -- One idea of optimizing this is to look closely at the graphs and try to guess what variables can be collapsed.
    whenM sizePreservationOption $ billTo [Benchmark.TypeBasedTermination, Benchmark.Preservation] refinePreservedVariables

    reportSDoc "term.tbt" 10 $ vcat $ "Clause constraints:" : (map (nest 2 . text . show) newConstraints)
    rigids <- getCurrentRigids
    bottomVars <- getBottomVariables
    infiniteVars <- getInfiniteSizes
    reportSDoc "term.tbt" 40 $ vcat $ map (nest 2)
      [ "Rigid context:       " <+> pretty rigids
      , "undefined sizes:     " <+> text (show infiniteVars)
      ]

    reportSDoc "term.tbt" 60 $ vcat $ map (nest 2)
      [ "Bottom vars:         " <+> text (show bottomVars)
      , "Arity:               " <+> text (show arity)
      ]

    subst <- simplifySizeGraph rigids newConstraints

    reportSDoc "term.tbt" 10 $ vcat $
      "Substitution of local size variables:" :
      map (\(i, e) -> nest 2 $ pretty (SDefined i) <+> "↦" <+> pretty e) (IntMap.toList subst)
    pure subst

-- | Given a set of names, launches size-checking on a mutual block. Returns a set of call matrices with a possibly size-preserving signature, or an error.
invokeSizeChecker :: QName -> Set QName -> TBTM (IntMap SizeExpression, SizeSignature) -> TCM (Either [String] (CallGraph CallPath, SizeSignature))
invokeSizeChecker rootName nms action = do
  ((subst, sizePreservationInferenceResult), totalGraph, errorMessages, calls) <- runSizeChecker rootName nms action

  reportSDoc "term.tbt" 60 $ vcat $
    [ text "Total graph:" ] ++
    map (nest 2 . text . show) totalGraph
  let indexing = zip (Set.toList nms) [0..]

  case errorMessages of
    [] -> do
      -- No internal errors, let's proceed with building size-change matrices
      edges <- forM calls (\mrc -> do
            let q1 = mrcNameFrom mrc
                q2 = mrcNameTo mrc
                sizes1 = mrcSizesFrom mrc
                sizes2 = mrcSizesTo mrc
                place = mrcPlace mrc
                matrix = makeCM (length sizes1) (length sizes2) (List.transpose $ composeMatrix subst sizes1 sizes2)
                n = fromJust $ List.lookup q1 indexing
                m = fromJust $ List.lookup q2 indexing
            reportSDoc "term.tbt" 20 $ vcat
              [ "Matrix between" <+> prettyTCM q1 <+> text ("(" ++ show sizes1 ++ ")") <+> "and" <+> prettyTCM q2 <+> text ("(" ++ show sizes2 ++ ")")
              , pretty matrix
              ]
            pure $ Edge n m $ singleton $ CallMatrixAug matrix $ CallPath $ fromList [CallInfo q2 place])
      pure $ Right (fromList edges, sizePreservationInferenceResult)
    l -> pure $ Left l

-- | Populates a set of rigid variables and internal context according to the LHS of a clause.
--   Returns the expected type of a clause, which may be different from semi-applied function type because of copatterns
encodeFunctionClause :: SizeType -> Clause -> TBTM SizeType
encodeFunctionClause sizeType c = do
  let patterns = namedClausePats c
  reportSDoc "term.tbt" 10 $ vcat
    [ "Starting encoding of a clause: " <+> prettyTCM c
    , "  Type of the function: " <+> pretty sizeType
    ]
  (leafVariables, tele) <- matchPatterns sizeType patterns
  setLeafSizeVariables leafVariables
  patternContext <- getCurrentCoreContext
  sizeContext <- getCurrentRigids
  reportSDoc "term.tbt" 10 $ vcat
    [ "Finished encoding of clause: " <+> prettyTCM c
    , "  Var context :              " <+> pretty patternContext
    , "  Rigid variables:           " <+> pretty sizeContext
    , "  Expected type of clause:   " <+> pretty tele
    ]
  reportSDoc "term.tbt" 60 $ vcat
    [ "  Leaf variables:          " <+> text (show leafVariables)
    ]
  return tele


encodeDataType :: [QName] -> Set QName -> Bool -> Bool -> [Polarity] -> Type -> TCM SizeSignature
encodeDataType ctors fullSet generify isCoinductiveRecord polarities tp = do
  let TelV domains codomain = telView' tp
  -- We need to check if a datatype is actually recursive
  -- This helps a lot for performance, since it allows us to not introduce a lot of superfluous size variables,
  -- which in turn makes the graph solving faster.
  isRecursiveData <- anyM ctors (checkRecursiveConstructor fullSet)

  pure $ SizeSignature
         (if isRecursiveData then [SizeUnbounded] else [])
         (if isCoinductiveRecord && isRecursiveData then [0] else [])
         (encodeDatatypeDomain isRecursiveData generify polarities [] domains)

-- | 'checkRecursiveConstructor allNames qn' checks that a construtor with the name 'qn' refers to any of the 'allNames',
-- thus giving us the information if this constructor is recursive.
checkRecursiveConstructor :: Set QName -> QName -> TCM Bool
checkRecursiveConstructor allNames qn = do
  conType <- defType <$> getConstInfo qn
  (TelV dom _) <- telView conType
  findMention dom
  where
    findMention :: Tele (Dom Type) -> TCM Bool
    findMention EmptyTel = pure False
    findMention (ExtendTel dt rest) = findMentionInTerm (unEl (unDom dt)) `or2M` findMention (unAbs rest)

    findMentionInTerm :: Term -> TCM Bool
    findMentionInTerm t = case t of
      (Def qn elims) -> pure (qn `Set.member` allNames) `or2M` findMentionInElims elims
      (Pi dom cod) -> (findMentionInTerm (unEl (unDom dom))) `or2M` (findMentionInTerm (unEl (unAbs cod)))
      (Lam _ cod) -> findMentionInTerm (unAbs cod)
      (Sort _) -> pure False
      (Var _ elims) -> findMentionInElims elims
      (MetaV _ _) -> pure False
      (Level _) -> pure False
      (Lit _) -> pure False
      (DontCare _) -> pure False
      (Con _ _ elims) -> findMentionInElims elims
      (Dummy _ _) -> pure False

    findMentionInElims :: Elims -> TCM Bool
    findMentionInElims elims = (anyM elims (\case
      Apply arg -> findMentionInTerm $ unArg arg
      _ -> pure False))

-- | Converts the telescope of a datatype to a size type.
encodeDatatypeDomain :: Bool -> Bool -> [Polarity] -> [Bool] -> Tele (Dom Type) -> SizeType
encodeDatatypeDomain isRecursive _ polarities params EmptyTel =
  let size = if isRecursive then SDefined 0 else SUndefined
      -- tail because scanl inserts the given starting element in the beginning
      treeArgs = List1.tail $ List1.scanl
              (\(ind, t) isGeneric -> if isGeneric then (ind + 1, SizeGenericVar 0 ind) else (ind, UndefinedSizeType))
              (0, UndefinedSizeType)
              params
      actualArgs = zip polarities (reverse (map snd treeArgs))
  in SizeTree size actualArgs
encodeDatatypeDomain isRecursive generify polarities params (ExtendTel dt rest) =
  let d = unEl $ unDom dt
      genericArity = inferGenericArity d
      (wrapper, newParam) = if generify
        then case genericArity of
          Just arity -> (SizeGeneric arity, True)
          Nothing -> (SizeArrow UndefinedSizeType, False)
        else (SizeArrow UndefinedSizeType, False)
      tails = encodeDatatypeDomain isRecursive generify polarities (newParam : params) (unAbs rest)
  in wrapper tails
  where
    inferGenericArity :: Term -> Maybe Int
    inferGenericArity (Sort _) = Just 0
    inferGenericArity (Pi _ rest) = fmap (+ 1) (inferGenericArity $ unEl $ unAbs rest)
    inferGenericArity _ = Nothing

-- | Builds a size-change matrix based on relation between substituted flexible variables ('rs') and initial rigid variables ('ls')
composeMatrix :: IntMap SizeExpression -> [Int] -> [Int] -> [[Order]]
composeMatrix subst ls rs = [ [ obtainOrder l (subst IntMap.!? r) | r <- rs ] | l <- ls ]

-- | Given a cluster 'i', returns the relation of a size expression with the cluster.
obtainOrder :: Int -> Maybe SizeExpression -> Order
obtainOrder  i Nothing = Order.unknown
obtainOrder  i (Just (SEMeet list))
  | i >= length list    = Order.unknown
  | list List.!! i == i = Order.le
  | list List.!! i > 0  = Order.lt
  | otherwise           = Order.unknown

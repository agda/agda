-- | This module contains the implementation of Mimer, the current
-- implementation of the auto interactive command (C-c C-a) and the successor of
-- Agsy.
--
-- The overall idea is that Mimer gathers a collection of "components" that it
-- could use for building a solution and tries to refine the goal iteratively
-- using these components. Components include global definitions, local variables,
-- let-bound variables, and recursive calls to the function being defined.
--
-- Mimer manages multiple branches of the search at the same time and assigns a
-- cost to each branch, which is the sum of the costs of all its components. The
-- cost of a component in turn is determined by its type and the number of new
-- metas it introduces.
--
-- A branch can be refined by picking one of its unsolved metavariables and
-- refining it with all available components, resulting in a number of new
-- branches (each one with a higher cost than the original).
--
-- Mimer iteratively refines the branch with the lowest cost until it finds a
-- solution or runs out of time.

module Agda.Mimer.Mimer
  ( MimerResult(..)
  , mimer
  )
  where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (ReaderT(..), runReaderT, asks, ask, lift)
import Data.Functor ((<&>))
import Data.List ((\\))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (maybeToList)
import Data.PQueue.Min (MinQueue)
import qualified Data.PQueue.Min as Q

import qualified Agda.Benchmarking as Bench
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Info (pattern UnificationMeta)
import Agda.Syntax.Internal
import Agda.Syntax.Position (Range, noRange)
import Agda.Syntax.Translation.InternalToAbstract (reify, blankNotInScope)

import Agda.TypeChecking.Primitive (getBuiltinName)
import Agda.TypeChecking.Empty (isEmptyType)
import Agda.TypeChecking.Level (levelType)
import Agda.TypeChecking.MetaVars (newValueMeta)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce (reduce, instantiateFull, instantiate)
import Agda.TypeChecking.Rules.Term  (makeAbsurdLambda)
import Agda.TypeChecking.Substitute (apply, NoSubst(..))

import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Maybe (catMaybes)
import Agda.Utils.Monad (ifM)
import Agda.Utils.Null
import Agda.Utils.Tuple (mapFst, mapSnd)
import Agda.Utils.Time (getCPUTime, fromMilliseconds)

import Data.IORef (readIORef, newIORef)

import Agda.Interaction.Base (Rewrite(..))
import Agda.Interaction.BasicOps (normalForm)
import Agda.Utils.Monad (concatMapM)

import Agda.Mimer.Types
import Agda.Mimer.Monad
import Agda.Mimer.Options

-- IDEA for implementing case-splitting:
--  1. Modify the collectRecVarCandidates to get all variables.
--  2. Go through all variables to see if they are data types (not records)
--  3. Run makeCase for those variables.
--  4. Find out how to get the new interaction points/metas from the cases
--  5. After search is done, compute out-of-scope variables.
--  6. Run make-case again to introduce those variables.
--  7. Redo the reification in the new clauses.
--  8. Return the new clauses and follow Auto for insertion.

-- | Entry point.
--   Run Mimer on the given interaction point, returning the desired solution(s).
--   Also debug prints timing statistics.
mimer :: MonadTCM tcm
  => Rewrite         -- ^ Degree of normalization of solution terms.
  -> InteractionId   -- ^ Hole to run on.
  -> Range           -- ^ Range of hole (for parse errors).
  -> String          -- ^ Content of hole (to parametrize Mimer).
  -> tcm MimerResult
mimer norm ii rng argStr = liftTCM $ do
    reportSDoc "mimer.top" 10 do
      "Running Mimer on interaction point" <+> pretty ii <+> "with argument string" <+> text (show argStr)

    start <- liftIO $ getCPUTime

    opts <- parseOptions ii rng argStr
    reportS "mimer.top" 15 ("Mimer options: " ++ show opts)

    -- Andreas, 2025-04-16, changing the plain getTC/putTC bracket to localTCState.
    -- localTCState should be used by default,
    -- it keeps the Statistics about metas and constraints.
    -- Was there a reason to use plain getTC/putTC or is it "don't care" since
    -- mimer is an interactive command and no one looks at the statistics?
    sols <- localTCState $ runSearch norm opts ii rng

    -- Turn the solutions into the desired results (first solution or list of solutions).
    sol <- case drop (optSkip opts) $ zip [0..] sols of
          [] -> do
            reportSLn "mimer.top" 10 "No solution found"
            return MimerNoResult
          sols' | optList opts -> pure $ MimerList [ (i, s) | (i, MimerExpr s) <- sols' ]
          (_, sol) : _ -> do
            reportSDoc "mimer.top" 10 $ "Solution:" <+> prettyTCM sol
            return sol

    -- Print timing statistic.
    stop <- liftIO $ getCPUTime
    let time = stop - start
    reportSDoc "mimer.top" 10 ("Total elapsed time:" <+> pretty time)
    verboseS "mimer.stats" 50 $ writeTime ii (if null sols then Nothing else Just time)

    return sol


-- Order to try things in:
-- 1. Local variables (including let-bound)
-- 2. Data constructors
-- 3. Where clauses
-- 4. Lambda abstract
-- Other: Equality, empty type, record projections
-- - If we only use constructors if the target type is a data type, we might
--   generate η-reducible expressions, e.g. λ xs → _∷_ 0 xs


------------------------------------------------------------------------------
-- * Core algorithm
------------------------------------------------------------------------------

runSearch :: Rewrite -> Options -> InteractionId -> Range -> TCM [MimerResult]
runSearch norm options ii rng = withInteractionId ii $ do
  (mTheFunctionQName, whereNames) <- fmap ipClause (lookupInteractionPoint ii) <&> \case
    clause@IPClause{} -> ( Just $ ipcQName clause
                         , case A.whereDecls $ A.clauseWhereDecls $ ipcClause clause of
                             Just decl -> declarationQnames decl
                             _ -> []
                         )
    IPNoClause -> (Nothing, [])

  reportSDoc "mimer.init" 15 $ "Interaction point in function:" <+> pretty mTheFunctionQName
  reportSDoc "mimer.init" 25 $ "Names in where-block" <+> pretty whereNames

  metaId <- lookupInteractionId ii
  metaVar <- lookupLocalMeta metaId

  -- We want to be able to solve with recursive calls
  setMetaOccursCheck metaId DontRunMetaOccursCheck

  metaIds <- case mvInstantiation metaVar of
    InstV inst -> do

      metaIds <- allOpenMetas (instBody inst)

      -- TODO: Make pretty instantiation for 'Instantiation'?
      reportSDoc "mimer.init" 20 $ sep [ "Interaction point already instantiated:" <+> pretty (instBody inst)
                                       , "with args" <+> pretty (instTel inst) ]

      -- ctx <- getContextTelescope
      -- #7402: still solve the top-level meta, because we don't have the correct contexts for the
      --        submetas
      return [metaId | not $ null metaIds]
    OpenMeta UnificationMeta -> do
      reportSLn "mimer.init" 20 "Interaction point not instantiated."
      return [metaId]
    _ -> __IMPOSSIBLE__
  -- TODO: Print each meta-variable's full context telescope
  reportSDoc "mimer.init" 20 $ "Remaining meta-variables to solve:" <+> prettyTCM metaIds
  reportSDoc "mimer.init" 20 $ "Meta var args" <+> (prettyTCM =<< getMetaContextArgs metaVar)


  fnArgs1 <- withShowAllArguments' False $ getContextArgs >>= mapM prettyTCM
  fnArgs2 <- withShowAllArguments' True  $ getContextArgs >>= mapM prettyTCM
  let bringScope = map snd $ filter (uncurry (/=)) $ zip fnArgs1 fnArgs2
      bringScopeNoBraces = map (filter (`notElem` ['{', '}']) . P.render) bringScope
  reportSDoc "mimer.temp" 20 $ vcat
    [ "Things to bring into scope:"
    , nest 2 $ vcat
      [ "Context args (don't show):" <+> pretty fnArgs1
      , "Context args (show all):  " <+> pretty fnArgs2
      , "To bring into scope:      " <+> pretty bringScope
      , "To bring into scope (str):" <+> pretty bringScopeNoBraces
      ]
    ]

  -- Check if there are any meta-variables to be solved
  case metaIds of
    -- No variables to solve, return the instantiation given
    [] -> do
      case mvInstantiation metaVar of
        InstV inst -> do
          expr <- withInteractionId ii $ do
            metaArgs <- getMetaContextArgs metaVar
            instantiateFull (apply (MetaV metaId []) metaArgs) >>= normalForm norm >>= reify
          str <- P.render <$> prettyTCM expr
          let sol = MimerExpr str
          reportSDoc "mimer.init" 10 $ "Goal already solved. Solution:" <+> text str
          return [sol]
        _ -> __IMPOSSIBLE__
    _ -> do
      costs <- ifM (hasVerbosity "mimer.cost.custom" 10)
                 {- then -} customCosts
                 {- else -} (return defaultCosts)
      reportSDoc "mimer.cost.custom" 10 $ "Using costs:" $$ nest 2 (pretty costs)
      components <- collectComponents options costs ii mTheFunctionQName whereNames metaId
      let startGoals = map Goal metaIds

      state <- getTC
      env <- askTC

      let startBranch = SearchBranch
            { sbTCState = state
            , sbGoals = startGoals
            , sbCost = 0
            , sbCache = Map.empty
            , sbComponentsUsed = Map.empty
            }

      statsRef <- liftIO $ newIORef emptyMimerStats
      checkpoint <- viewTC eCurrentCheckpoint
      mflat <- getBuiltinName BuiltinFlat
      let searchOptions = SearchOptions
            { searchBaseComponents = components
            , searchHintMode = optHintMode options
            , searchTimeout = optTimeout options
            , searchGenProjectionsLocal = True
            , searchGenProjectionsLet = True
            , searchGenProjectionsExternal = False
            , searchGenProjectionsRec = True
            , searchSpeculateProjections = True
            , searchTopMeta = metaId
            , searchTopEnv = env
            , searchTopCheckpoint = checkpoint
            , searchInteractionId = ii
            , searchFnName = mTheFunctionQName
            , searchCosts = costs
            , searchStats = statsRef
            , searchRewrite = norm
            , searchBuiltinFlat = mflat
            }

      reportSDoc "mimer.init" 20 $ "Using search options:" $$ nest 2 (prettyTCM searchOptions)
      reportSDoc "mimer.init" 20 $ "Initial search branch:" $$ nest 2 (pretty startBranch)

      flip runReaderT searchOptions $ bench [] $ do

        -- TODO: Check what timing stuff is used in Agda.Utils.Time
        timeout <- fromMilliseconds <$> asks searchTimeout
        startTime <- liftIO getCPUTime
        let go :: Int -> Int -> MinQueue SearchBranch -> SM ([MimerResult], Int)
            go 0 n _ = pure ([], n)
            go need n branchQueue = case Q.minView branchQueue of
              Nothing -> do
                reportSLn "mimer.search" 30 $ "No remaining search branches."
                return ([], n)
              Just (branch, branchQueue') -> do
                time <- liftIO getCPUTime
                mimerTrace 0 10 $ vcat
                  [ "Choosing branch"
                  , nest 2 $ sep
                    [ branchInstantiationDocCost branch <> ","
                    , nest 2 $ "metas:" <+> prettyTCM (map goalMeta $ sbGoals branch)
                    ]
                  ]
                reportSDoc "mimer.search" 50 $ "Full branch:" <+> pretty branch
                reportSMDoc "mimer.search" 50 $
                  "Instantiation of other branches:" <+> prettyList (map branchInstantiationDocCost $ Q.toAscList branchQueue')

                let elapsed = time - startTime
                if elapsed < timeout
                then do
                  (newBranches, sols) <- refine branch >>= partitionStepResult
                  let branchQueue'' = foldr Q.insert branchQueue' newBranches
                  reportSLn "mimer.search" 40 $ show (length sols) ++ " solutions found during cycle " ++ show (n + 1)
                  reportSMDoc "mimer.search" 45 $ "Solutions:" <+> prettyTCM sols
                  mimerTrace 0 40 $ vcat
                     [ "Cycle" <+> pretty (n + 1) <+> "branches"
                     , nest 2 $ vcat $ map branchInstantiationDocCost $ Q.toAscList branchQueue''
                     ]
                  unless (null sols) $ mimerTrace 0 20 $ vcat
                     [ "Cycle" <+> pretty (n + 1) <+> "solutions"
                     , nest 2 $ vcat $ map prettyTCM sols
                     ]

                  let sols' = take need sols
                  mapFst (sols' ++) <$> go (need - length sols') (n + 1) branchQueue''
                else do
                  reportSLn "mimer.search" 30 $ "Search time limit reached. Elapsed search time: " ++ show elapsed
                  return ([], n)
        let numSolutions | optList options = 10 + optSkip options
                         | otherwise       = 1 + optSkip options
        (sols, nrSteps) <- go numSolutions 0 $ Q.singleton startBranch
        reportSLn "mimer.search" 20 $ "Search ended after " ++ show (nrSteps + 1) ++ " cycles"
        -- results <- liftTCM $ mapM exprToStringAndVars sols
        reportSDoc "mimer.search" 15 $ "Solutions found: " <+> prettyList (map prettyTCM sols)
        reportSMDoc "mimer.stats" 10 $ do
          ref <- asks searchStats
          stats <- liftIO $ readIORef ref
          "Statistics:" <+> text (show stats)
        return sols

-- | If there is no cache entry for the checkpoint, create one. If there already
-- is one, even if the components are not yet generated for some entries, it is
-- returned as is.
prepareComponents :: Goal -> SearchBranch -> SM (SearchBranch, [(Component, [Component])])
prepareComponents goal branch = withBranchAndGoal branch goal $ do
  reportSDoc "mimer.components" 50 $ "Preparing components for goal" <+> prettyTCM (goalMeta goal)
  checkpoint <- viewTC eCurrentCheckpoint
  -- Check if we there is something in the cache for this checkpoint
  comps <- case Map.lookup checkpoint (sbCache branch) of
    -- No, generate components from scratch
    Nothing -> do
      updateStat incCompRegen
      reportSDoc "mimer.components" 20 $ vcat
        [ "No cache found checkpoint:" <+> pretty checkpoint
        , nest 2 $ "with context:" <+> (inTopContext . prettyTCM =<< getContextTelescope) ]
      -- Generate components for this context
      comps <- genComponents
      reportSDoc "mimer.components" 20 $ "Generated" <+> pretty (sum $ map (length . snd) comps) <+> "components"
      return comps
    -- Yes, just update the missing generated components
    Just cache -> mapM prepare (Map.toAscList cache)
  let newCache = Map.fromList $ map (mapSnd Just) comps
  branch' <- updateBranch [] branch{sbCache = Map.insert checkpoint newCache (sbCache branch)}
  return (branch', comps)
  where
  prepare :: (Component, Maybe [Component]) -> SM (Component, [Component])
  prepare (sourceComp, Just comps) = do
    updateStat incCompNoRegen
    return (sourceComp, comps)
  prepare (sourceComp, Nothing) = do
    updateStat incCompRegen
    (sourceComp,) <$> genComponentsFrom True sourceComp

genComponents :: SM [(Component, [Component])]
genComponents = do
  opts <- ask
  let comps = searchBaseComponents opts
  n <- localVarCount
  localVars <- lift (getLocalVars n (costLocal $ searchCosts opts))
    >>= genAddSource (searchGenProjectionsLocal opts)
  recCalls <- genAddSource (searchGenProjectionsRec opts) (maybeToList $ hintThisFn comps)
  letVars <- mapM getOpenComponent (hintLetVars comps)
    >>= genAddSource (searchGenProjectionsLet opts)
  fns <- genAddSource (searchGenProjectionsExternal opts) (hintFns comps)
  axioms <- genAddSource (searchGenProjectionsExternal opts) (hintAxioms comps)
  return $ localVars ++ letVars ++ recCalls ++ fns ++ axioms
  where
    genAddSource :: Bool -> [Component] -> SM [(Component, [Component])]
    genAddSource genProj = mapM (\comp -> (comp,) <$> genComponentsFrom genProj comp)


genComponentsFrom :: Bool -- ^ Apply record elimination
                  -> Component
                  -> SM [Component]
genComponentsFrom appRecElims origComp = do
  reportSDoc "mimer.components" 50 $ "Generating components from original component" <+> prettyTCM (compId origComp) <+> prettyTCM (compName origComp)
  comps <- if | compRec origComp -> mapM (applyToMetasG Nothing) =<< genRecCalls origComp
              | otherwise        -> (:[]) <$> applyToMetasG Nothing origComp
  if appRecElims
  then concat <$> mapM (applyProjections Set.empty) comps
  else return comps
  where
  applyProjections :: Set QName -> Component -> SM [Component]
  applyProjections seenRecords comp = do
    projComps <- getRecordInfo (compType comp) >>= \case
      Nothing -> return []
      Just (recordName, args, fields, isRecursive)
          | Set.member recordName seenRecords -> do
              reportSDoc "mimer.components" 60 $
                "Skipping projection because recursive record already seen:" <+> pretty recordName
              return []
          | otherwise -> do
              let seenRecords' = if isRecursive then Set.insert recordName seenRecords else seenRecords
              comps <- mapM (applyProj args comp >=> applyToMetasG Nothing) fields
              concatMapM (applyProjections seenRecords') comps
    return $ comp : projComps

genRecCalls :: Component -> SM [Component]
genRecCalls thisFn = do
  reportSDoc "mimer.components.open" 40 $ "Generating recursive calls for component" <+> prettyTCM (compId thisFn) <+> prettyTCM (compName thisFn)
  reportSDoc "mimer.components.open" 60 $ "  checkpoint =" <+> (prettyTCM =<< viewTC eCurrentCheckpoint)
  -- TODO: Make sure there are no pruning problems
  asks (hintRecVars . searchBaseComponents) >>= getOpen >>= \case
    -- No candidate arguments for a recursive call
    [] -> return []
    recCandTerms -> do
      Costs{..} <- asks searchCosts
      n <- localVarCount
      localVars <- lift $ getLocalVars n costLocal
      let recCands = [ (t, i) | t@(compTerm -> v@Var{}) <- localVars, NoSubst i <- maybeToList $ lookup v recCandTerms ]

      let newRecCall = do
            -- Apply the recursive call to new metas
            (thisFnTerm, thisFnType, newMetas) <- lift $ applyToMetas 0 (compTerm thisFn) (compType thisFn)
            let argGoals = map Goal newMetas
            comp <- newComponent newMetas (compCost thisFn) (compName thisFn) 0 thisFnTerm thisFnType
            return (comp, zip argGoals [0..])

          -- go :: Component -- ^ Recursive call function applied to meta-variables
          --   -> [(Goal, Int)] -- ^ Remaining parameters to try to fill
          --   -> [(Component, Int)] -- ^ Remaining argument candidates for the current parameter
          --   -> SM [Component]
          go _thisFn [] _args = return []
          go thisFn (_ : goals) [] = go thisFn goals recCands
          go thisFn ((goal, i) : goals) ((arg, j) : args) | i == j = do
            reportSMDoc "mimer.components.rec" 80 $ hsep
              [ "Trying to generate recursive call"
              , prettyTCM (compTerm thisFn)
              , "with" <+> prettyTCM (compTerm arg)
              , "for" <+> prettyTCM (goalMeta goal) ]
            goalType <- getMetaTypeInContext (goalMeta goal)
            state <- getTC
            tryRefineWith' goal goalType arg >>= \case
              Nothing -> do
                putTC state
                go thisFn ((goal, i) : goals) args
              Just (newMetas1, newMetas2) -> do
                let newComp = thisFn{compMetas = newMetas1 ++ newMetas2 ++ (compMetas thisFn \\ [goalMeta goal])}
                (thisFn', goals') <- newRecCall
                (newComp:) <$> go thisFn' (drop (length goals' - length goals - 1) goals') args
          go thisFn goals (_ : args) = go thisFn goals args
      (thisFn', argGoals) <- newRecCall
      comps <- go thisFn' argGoals recCands
      -- Compute costs for the calls:
      --  - costNewMeta/costNewHiddenMeta for each unsolved argument
      --  - zero for solved arguments
      --  - costLocal for the parameter we recurse on
      let callCost comp = (costLocal +) . sum <$> argCosts (compTerm comp)
          argCosts (Def _ elims) = mapM argCost elims
          argCosts _ = __IMPOSSIBLE__
          argCost (Apply arg) = instantiate arg <&> \ case
            Arg h MetaV{} | visible h -> costNewMeta
                          | otherwise -> costNewHiddenMeta
            _ -> 0
          argCost Proj{}   = pure 0
          argCost IApply{} = pure 0
      mapM (\ c -> (`addCost` c) <$> callCost c) comps


refine :: SearchBranch -> SM [SearchStepResult]
refine branch = withBranchState branch $ do
  let (goal1, branch1) = nextGoal branch

  withBranchAndGoal branch1 goal1 $ do
    goalType1 <- bench [Bench.Reduce] $ reduce =<< getMetaTypeInContext (goalMeta goal1)

    mimerTrace 1 10 $ sep
      [ "Refining goal"
      , nest 2 $ prettyTCM (goalMeta goal1) <+> ":" <+> prettyTCM goalType1
      , nest 2 $ "in context" <+> (inTopContext . prettyTCM =<< getContextTelescope)
      ]

    reportSDoc "mimer.refine" 30 $ "Goal type:" <+> pretty goalType1
    reportSDoc "mimer.refine" 30 $ "Goal context:" <+> (pretty =<< getContextTelescope)

    -- Lambda-abstract as far as possible
    tryLamAbs goal1 goalType1 branch1 >>= \case
      -- Absurd lambda
      Left branch2 -> do
        mimerTrace 1 10 $ sep
              [ "Absurd bambda refinement", nest 2 $ prettyGoalInst goal1 ]
        args <- map Apply <$> getContextArgs
        e <- blankNotInScope =<< reify (MetaV (goalMeta goal1) args)
        return [ResultExpr e]
      -- Normal abstraction
      Right (goal2, goalType2, branch2) -> withBranchAndGoal branch2 goal2 $ do
        (branch3, components) <- prepareComponents goal2 branch2
        withBranchAndGoal branch3 goal2 $ do

          when (goalMeta goal2 /= goalMeta goal1) $ do
            mimerTrace 1 10 $ sep
              [ "Lambda refinement", nest 2 $ prettyGoalInst goal1 ]
            mimerTrace 1 10 $ sep
              [ "Refining goal"
              , nest 2 $ prettyTCM (goalMeta goal2) <+> ":" <+> prettyTCM goalType2
              , nest 2 $ "in context" <+> (inTopContext . prettyTCM =<< getContextTelescope)
              ]

          mimerTrace 2 40 $ vcat
            [ "Components:"
            , nest 2 $ vcat $ map prettyTCM $ concatMap snd components
            ]

          results1 <- tryComponents goal2 goalType2 branch3 components
          results2 <- tryDataRecord goal2 goalType2 branch3
          return $ results1 ++ results2

tryComponents :: Goal -> Type -> SearchBranch -> [(Component, [Component])] -> SM [SearchStepResult]
tryComponents goal goalType branch comps = withBranchAndGoal branch goal $ do
  checkpoint <- viewTC eCurrentCheckpoint
  let tryFor (sourceComp, comps') = do
        -- Clear out components that depend on meta-variables that have been used.
        let newCache = Map.insert sourceComp Nothing (sbCache branch Map.! checkpoint)
        newBranches <- catMaybes <$> mapM (tryRefineWith goal goalType branch) comps'
        return $ map (\br -> br{sbCache = Map.insert checkpoint newCache (sbCache branch)}) newBranches
  newBranches <- concatMapM tryFor comps
  mapM checkSolved newBranches

-- | Returns @Right@ for normal lambda abstraction and @Left@ for absurd lambda.
tryLamAbs :: Goal -> Type -> SearchBranch -> SM (Either SearchBranch (Goal, Type, SearchBranch))
tryLamAbs goal goalType branch =
  case unEl goalType of
    Pi dom abs -> isEmptyType (unDom dom) >>= \case
      True -> do
        f <- liftTCM $ makeAbsurdLambda noRange dom abs
        args <- map Apply <$> getContextArgs
        newMetaIds <- assignMeta (goalMeta goal) (Def f args) goalType
        Left <$> updateBranch newMetaIds branch
      False -> do
        reportSDoc "mimer.lam" 40 $ "Trying lambda abstraction for pi type" <+> prettyTCM goalType
        let abs' | isNoName (absName abs) = abs { absName = "z" }
                 | otherwise = abs
        (metaId', bodyType, metaTerm, env) <- underAbstractionAbs dom abs' $ \bodyType -> do
          reportSDoc "mimer.lam" 40 $ "  bodyType = " <+> prettyTCM bodyType
          bodyType <- bench [Bench.Reduce] $ reduce bodyType -- TODO: Good place to reduce?
          reportSDoc "mimer.lam" 40 $ "  bodyType (reduced) = " <+> prettyTCM bodyType
          (metaId', metaTerm) <- bench [Bench.Free] $ newValueMeta DontRunMetaOccursCheck CmpLeq bodyType
          reportSDoc "mimer.lam" 40 $ "  metaId' = " <+> prettyTCM metaId'
          env <- askTC
          return (metaId', bodyType, metaTerm, env)

        let argInf = domInfo dom -- TODO: is this the correct arg info?
            newAbs = Abs (absName abs') metaTerm
            -- look at mkLam
            term = Lam argInf newAbs

        newMetaIds <- assignMeta (goalMeta goal) term goalType

        withEnv env $ do
          branch' <- updateBranch newMetaIds branch
          tryLamAbs (Goal metaId') bodyType branch'
    _ -> done
  where
    done = do
      branch' <- updateBranch [] branch -- TODO: Is this necessary?
      return $ Right (goal, goalType, branch')

-- TODO: Factor out `checkSolved`
tryDataRecord :: Goal -> Type -> SearchBranch -> SM [SearchStepResult]
tryDataRecord goal goalType branch = withBranchAndGoal branch goal $ do
  -- TODO: There is a `isRecord` function, which performs a similar case
  -- analysis as here, but it does not work for data types.
  case unEl goalType of
    Def qname elims -> theDef <$> getConstInfo qname >>= \case
      recordDefn@Record{} -> do
        tryRecord recordDefn
      dataDefn@Datatype{} -> do
        tryData dataDefn
      primitive@Primitive{} -> do
        return []
      -- TODO: Better way of checking that type is Level
      Axiom{}
        | P.prettyShow qname == "Agda.Primitive.Level" -> do
            tryLevel
        | otherwise -> do
        return []
      DataOrRecSig{} -> do
        return []
      GeneralizableVar{} -> do
        return []
      AbstractDefn{} -> do
        return []
      Function{} -> do
        return []
      Constructor{} -> do
        return []
      PrimitiveSort{} -> do
        return []
    Sort (Type level) -> do
      trySet level
    Sort sort -> do
      return []
    _ -> return []
  where
      -- TODO: Alternatively, the constructor can be accessed via `getRecordConstructor`
      -- TODO: There might be a neater way of applying the constructor to new metas
    tryRecord :: Defn -> SM [SearchStepResult]
    tryRecord recordDefn = do
      cost <- asks (costRecordCon . searchCosts) -- TODO: Use lenses for this?
      comp <- qnameToComponent cost $ conName $ recConHead recordDefn
      -- NOTE: at most 1
      newBranches <- maybeToList <$> tryRefineAddMetas goal goalType branch comp
      mapM checkSolved newBranches

    tryData :: Defn -> SM [SearchStepResult]
    tryData dataDefn = do
      let constructors = dataCons dataDefn
      reportSDoc "mimer.try" 40 $ hsep $ "tryData" : map prettyTCM constructors
      cost <- asks (costDataCon . searchCosts)
      comps <- mapM (qnameToComponent cost) constructors
      newBranches <- mapM (tryRefineAddMetas goal goalType branch) comps
      -- TODO: Reduce overlap between e.g. tryLocals, this and tryRecord
      mapM checkSolved (catMaybes newBranches)

    tryLevel :: SM [SearchStepResult]
    tryLevel = do
      levelHints <- asks (hintLevel . searchBaseComponents)
      newBranches <- catMaybes <$> mapM (tryRefineAddMetas goal goalType branch) levelHints
      mapM checkSolved newBranches

    -- TODO: Add an extra filtering on the sort
    trySet :: Level -> SM [SearchStepResult]
    trySet level = do
      reducedLevel <- reduce level
      cost <- asks (costSet . searchCosts)
      setCandidates <- case reducedLevel of
        (Max i [])
          | i > 0 -> do
              comp <- newComponent [] cost Nothing 0 (Sort $ Type $ Max (i - 1) []) goalType
              return [(branch, comp)]
          | otherwise -> return []
        (Max i ps) -> do
              (metaId, metaTerm) <- createMeta =<< levelType
              comp <- newComponent [metaId] cost Nothing 0 (Sort $ Type $ Max (max 0 (i - 1)) [Plus 0 metaTerm]) goalType
              branch' <- updateBranch [metaId] branch
              return [(branch', comp)]
      reportSDoc "mimer.refine.set" 40 $
        "Trying" <+> prettyTCM (map snd setCandidates) <+> "for" <+> prettyTCM goalType
      newBranches <- catMaybes <$> mapM (\(br,c) -> tryRefineWith goal goalType br c) setCandidates
      components <- asks searchBaseComponents
      newBranches' <- catMaybes <$> mapM (tryRefineAddMetas goal goalType branch)
                      (concatMap ($ components)
                       [ hintDataTypes
                       , hintRecordTypes
                       , hintAxioms])
      mapM checkSolved (newBranches ++ newBranches')

-- | Type should already be reduced here
-- NOTE: Does not reset the state!
-- TODO: Make sure the type is always reduced
tryRefineWith :: Goal -> Type -> SearchBranch -> Component -> SM (Maybe SearchBranch)
tryRefineWith goal goalType branch comp = withBranchAndGoal branch goal $ do

  metasCreatedBy (dumbUnifierErr (compType comp) goalType) >>= \case
    (Nothing, newMetaStore) -> do
      updateStat incRefineSuccess
      -- TODO: Why is newMetaIds not used here?
      newMetaIds <- assignMeta (goalMeta goal) (compTerm comp) goalType
      let newMetaIds' = Map.keys (openMetas newMetaStore)
      reportSDoc "mimer.refine" 60 $
        "Refine: assignMeta created new metas:" <+> prettyTCM newMetaIds

      reportSMDoc "mimer.refine" 50 $ "Refinement succeeded"

      mimerTrace 2 10 $ sep
        [ "Found refinement"
        , nest 2 $ sep [ prettyTCM (compTerm comp)
                       , ":" <+> prettyTCM (compType comp) ] ]
      -- Take the metas stored in the component and add them as sub-goals
      Just <$> updateBranchCost comp (newMetaIds' ++ compMetas comp) branch
    (Just err, _) -> do
      updateStat incRefineFail
      reportSMDoc "mimer.refine" 50 $ "Refinement failed"

      mimerTrace 2 60 $ vcat
        [ "Failed refinement"
        , nest 2 $ sep [ prettyTCM (compTerm comp)
                       , ":" <+> prettyTCM (compType comp) ]
        , nest 2 $ prettyTCM err ]
      return Nothing

tryRefineWith' :: Goal -> Type -> Component -> SM (Maybe ([MetaId], [MetaId]))
tryRefineWith' goal goalType comp = do
  metasCreatedBy (dumbUnifier (compType comp) goalType) >>= \case
    (True, newMetaStore) -> do
      newMetaIds <- assignMeta (goalMeta goal) (compTerm comp) goalType
      let newMetaIds' = Map.keys (openMetas newMetaStore)
      return $ Just (newMetaIds, newMetaIds')
    (False, _) -> return Nothing

-- TODO: Make policy for when state should be put
tryRefineAddMetas :: Goal -> Type -> SearchBranch -> Component -> SM (Maybe SearchBranch)
tryRefineAddMetas goal goalType branch comp = withBranchAndGoal branch goal $ do
  -- Apply the hint to new metas (generating @c@, @c ?@, @c ? ?@, etc.)
  -- TODO: Where is the best place to reduce the hint type?
  comp' <- applyToMetasG Nothing comp
  branch' <- updateBranch [] branch
  tryRefineWith goal goalType branch' comp'


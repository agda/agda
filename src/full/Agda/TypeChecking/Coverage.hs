{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE TypeApplications #-}

{-| Coverage checking, case splitting, and splitting for refine tactics.

 -}

module Agda.TypeChecking.Coverage
  ( SplitClause(..), clauseToSplitClause, insertTrailingArgs
  , Covering(..), splitClauses
  , coverageCheck
  , isCovered
  , splitClauseWithAbsurd
  , splitLast
  , splitResult
  , normaliseProjP
  ) where

import Prelude hiding (null, (!!))  -- do not use partial functions like !!

import Control.Monad
import Control.Monad.Except
import Control.Monad.Trans ( lift )

import Data.Foldable (for_)
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Internal hiding (DataOrRecord(..))
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Translation.InternalToAbstract (NamedClause(..))

import Agda.TypeChecking.Names
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.Monad

import Agda.TypeChecking.Rules.LHS (DataOrRecord(..), checkSortOfSplitVar)
import Agda.TypeChecking.Rules.LHS.Problem (allFlexVars)
import Agda.TypeChecking.Rules.LHS.Unify
import Agda.TypeChecking.Rules.Term (unquoteTactic)

import Agda.TypeChecking.Coverage.Match
import Agda.TypeChecking.Coverage.SplitTree
import Agda.TypeChecking.Coverage.SplitClause
import Agda.TypeChecking.Coverage.Cubical


import Agda.TypeChecking.Conversion (tryConversion, equalType)
import Agda.TypeChecking.Datatypes (getConForm)
import {-# SOURCE #-} Agda.TypeChecking.Empty ( checkEmptyTel, isEmptyTel, isEmptyType )
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Records
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Telescope.Path
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Warnings

import Agda.Interaction.Options

import Agda.Utils.Either
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.Tuple
import Agda.Utils.WithDefault

import Agda.Utils.Impossible
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Control.Monad.State


type CoverM = ExceptT SplitError TCM

-- | Top-level function for checking pattern coverage.
--
--   Effects:
--
--   - Marks unreachable clauses as such in the signature.
--
--   - Adds missing instances clauses to the signature.
--
coverageCheck
  :: QName     -- ^ Name @f@ of definition.
  -> Type      -- ^ Absolute type (including the full parameter telescope).
  -> [Clause]  -- ^ Clauses of @f@.  These are the very clauses of @f@ in the signature.
  -> TCM SplitTree
coverageCheck f t cs = do
  reportSLn "tc.cover.top" 30 $ "entering coverageCheck for " ++ prettyShow f
  reportSDoc "tc.cover.top" 75 $ "  of type (raw): " <+> (text . prettyShow) t
  reportSDoc "tc.cover.top" 45 $ "  of type: " <+> prettyTCM t
  TelV gamma a <- telViewUpTo (-1) t
  reportSLn "tc.cover.top" 30 $ "coverageCheck: computed telView"

  let -- n             = arity
      -- xs            = variable patterns fitting lgamma
      n            = size gamma
      xs           =  map (setOrigin Inserted) $ teleNamedArgs gamma

  reportSLn "tc.cover.top" 30 $ "coverageCheck: getDefFreeVars"

      -- The initial module parameter substitutions need to be weakened by the
      -- number of arguments that aren't module parameters.
  fv           <- getDefFreeVars f

  reportSLn "tc.cover.top" 30 $ "coverageCheck: getting checkpoints"

  -- TODO: does this make sense? Why are we weakening by n - fv?
  checkpoints <- applySubst (raiseS (n - fv)) <$> viewTC eCheckpoints

      -- construct the initial split clause
  let sc = SClause gamma xs idS checkpoints $ Just $ defaultDom a

  reportSDoc "tc.cover.top" 10 $ do
    let prCl cl = addContext (clauseTel cl) $
                  prettyTCMPatternList $ namedClausePats cl
    vcat
      [ text $ "Coverage checking " ++ prettyShow f ++ " with patterns:"
      , nest 2 $ vcat $ map prCl cs
      ]

  -- used = actually used clauses for cover
  -- pss  = non-covered cases
  CoverResult splitTree used pss qss noex <- cover f cs sc

  -- Andreas, 2018-11-12, issue #378:
  -- some indices in @used@ and @noex@ point outside of @cs@,
  -- since missing hcomp clauses have been added during the course of @cover@.
  -- We simply delete theses indices from @noex@.
  noex <- return $ List.filter (< length cs) $ IntSet.toList noex

  reportSDoc "tc.cover.top" 10 $ vcat
    [ "cover computed!"
    , text $ "used clauses: " ++ show used
    , text $ "non-exact clauses: " ++ show noex
    ]
  reportSDoc "tc.cover.splittree" 10 $ vcat
    [ "generated split tree for" <+> prettyTCM f
    , text $ prettyShow splitTree
    ]
  reportSDoc "tc.cover.covering" 10 $ vcat
    [ text $ "covering patterns for " ++ prettyShow f
    , nest 2 $ vcat $ map (\ cl -> addContext (clauseTel cl) $ prettyTCMPatternList $ namedClausePats cl) qss
    ]

  -- Storing the covering clauses so that checkIApplyConfluence_ can
  -- find them later.
  -- Andreas, 2019-03-27, only needed when --cubical
  -- Jesper, 2022-10-18, also needed for some backends, so keep when flag says so
  opts <- pragmaOptions
  when (isJust (optCubical opts) || optKeepCoveringClauses opts) $
    modifySignature $ updateDefinition f $ updateTheDef $ updateCovering $ const qss


  -- filter out the missing clauses that are absurd.
  pss <- flip filterM pss $ \(tel,ps) ->
    -- Andreas, 2019-04-13, issue #3692: when adding missing absurd
    -- clauses, also put the absurd pattern in.
    caseEitherM (checkEmptyTel noRange tel) (\ _ -> return True) $ \ l -> do
      -- Now, @l@ is the first type in @tel@ (counting from 0=leftmost)
      -- which is empty.  Turn it into a de Bruijn index @i@.
      let i = size tel - 1 - l
      -- Build a substitution mapping this pattern variable to the absurd pattern.
      let sub = inplaceS i $ absurdP i
        -- ifNotM (isEmptyTel tel) (return True) $ do
      -- Jesper, 2018-11-28, Issue #3407: if the clause is absurd,
      -- add the appropriate absurd clause to the definition.
      let cl = Clause { clauseLHSRange  = noRange
                      , clauseFullRange = noRange
                      , clauseTel       = tel
                      , namedClausePats = applySubst sub ps
                      , clauseBody      = Nothing
                      , clauseType      = Nothing
                      , clauseCatchall    = True       -- absurd clauses are safe as catch-all
                      , clauseExact       = Just False
                      , clauseRecursive   = Just False
                      , clauseUnreachable = Just False
                      , clauseEllipsis    = NoEllipsis
                      , clauseWhereModule = Nothing
                      }
      reportSDoc "tc.cover.missing" 20 $ inTopContext $ do
        sep [ "adding missing absurd clause"
            , nest 2 $ prettyTCM $ QNamed f cl
            ]
      reportSDoc "tc.cover.missing" 80 $ inTopContext $ vcat
        [ "l   = " <+> pretty l
        , "i   = " <+> pretty i
        , "cl  = " <+> pretty (QNamed f cl)
        ]
      addClauses f [cl]
      return False

  -- report a warning if there are uncovered cases,
  unless (null pss) $ do
    stLocalPartialDefs `modifyTCLens` Set.insert f
    whenM ((YesCoverageCheck ==) <$> viewTC eCoverageCheck) $
      setCurrentRange cs $ warning $ CoverageIssue f pss

  -- Andreas, 2017-08-28, issue #2723:
  -- Mark clauses as reachable or unreachable in the signature.
  -- Andreas, 2020-11-19, issue #5065
  -- Remember whether clauses are exact or not.
  let (is0, cs1) = unzip $ for (zip [0..] cs) $ \ (i, cl) -> let
          unreachable = i `IntSet.notMember` used
          exact       = i `IntSet.notMember` (IntSet.fromList noex)
        in (boolToMaybe unreachable i, cl
             { clauseUnreachable = Just unreachable
             , clauseExact       = Just exact
             })
  -- is = indices of unreachable clauses
  let is = catMaybes is0
  reportSDoc "tc.cover.top" 10 $ vcat
    [ text $ "unreachable clauses: " ++ if null is then "(none)" else show is
    ]
  -- Replace the first clauses by @cs1@.  There might be more
  -- added by @inferMissingClause@.
  modifyFunClauses f $ \ cs0 -> cs1 ++ drop (length cs1) cs0

  -- Warn if there are unreachable clauses and mark them as unreachable.
  unless (null is) $ do
    -- Warn about unreachable clauses.
    let unreached = filter ((Just True ==) . clauseUnreachable) cs1
    let ranges    = map clauseFullRange unreached
    setCurrentRange ranges $ warning $ UnreachableClauses f ranges

  -- report a warning if there are clauses that are not preserved as
  -- definitional equalities and --exact-split is enabled
  unless (null noex) $ do
      let noexclauses = map (indexWithDefault __IMPOSSIBLE__ cs1) noex
      setCurrentRange (map clauseLHSRange noexclauses) $
        warning $ CoverageNoExactSplit f $ noexclauses
  return splitTree

-- | Top-level function for eliminating redundant clauses in the interactive
--   case splitter
isCovered :: QName -> [Clause] -> SplitClause -> TCM Bool
isCovered f cs sc = do
  reportSDoc "tc.cover.isCovered" 20 $ vcat
    [ "isCovered"
    , nest 2 $ vcat $
      [ "f  = " <+> prettyTCM f
      , "cs = " <+> vcat (map (nest 2 . prettyTCM . NamedClause f True) cs)
      , "sc = " <+> prettyTCM sc
      ]
    ]
  -- Jesper, 2019-10: introduce trailing arguments (see #3828)
  (_ , sc') <- insertTrailingArgs True sc
  CoverResult { coverMissingClauses = missing } <- cover f cs sc'
  return $ null missing
 -- Andreas, 2019-08-08 and 2020-02-11
 -- If there is an error (e.g. unification error), don't report it
 -- to the user.  Rather, assume the clause is not already covered.
 `catchError` \ _ -> return False

-- | @cover f cs (SClause _ _ ps _) = return (splitTree, used, pss)@.
--   checks that the list of clauses @cs@ covers the given split clause.
--   Returns the @splitTree@, the @used@ clauses, and missing cases @pss@.
--
--   Effect: adds missing instance clauses for @f@ to signature.
--
cover :: QName -> [Clause] -> SplitClause ->
         TCM CoverResult
cover f cs sc@(SClause tel ps _ _ target) = updateRelevance $ do
  reportSDoc "tc.cover.cover" 10 $ inTopContext $ vcat
    [ "checking coverage of pattern:"
    , nest 2 $ prettyTCM sc
    , nest 2 $ "target sort =" <+> do addContext tel $ maybe (text "<none>") (prettyTCM . getSort . unDom) target
    ]
  reportSLn "tc.cover.cover" 80 $ "raw target =\n" ++ show target
  verboseS  "tc.cover.matching" 20 $ do
    reportSLn "tc.cover.matching" 20 $ "clauses when matching:"
    forM_ cs $ \ c -> do
      let gamma = clauseTel c
          ps = namedClausePats c
      reportSDoc "tc.cover.matching" 20 $ addContext gamma $
          "ps   :" <+> prettyTCM (fmap namedArg ps)

  match cs ps >>= \case
    Yes (i,mps) -> do
      reportSLn "tc.cover.cover" 10 $ "pattern covered by clause " ++ show i
      reportSDoc "tc.cover.cover" 20 $ text "with mps = " <+> do addContext tel $ pretty mps
      exact <- allM mps $ isTrivialPattern . snd
      let cl0 = indexWithDefault __IMPOSSIBLE__ cs i
      cl <- applyCl sc cl0 mps
      return $ CoverResult
        { coverSplitTree      = SplittingDone (size tel)
        , coverUsedClauses    = singleton i
        , coverMissingClauses = []
        , coverPatterns       = [cl]
        , coverNoExactClauses = IntSet.fromList [ i | not $ exact || clauseCatchall cl0 ]
        }

    No        ->  do
      reportSLn "tc.cover" 20 $ "pattern is not covered"
      let infer dom = isInstance dom || isJust (domTactic dom)
      if maybe False infer target
        then do
          -- Ulf, 2016-10-31: For now we only infer instance clauses. It would
          -- make sense to do it also for hidden, but since the value of a
          -- hidden clause is expected to be forced by later clauses, it's too
          -- late to add it now. If it was inferrable we would have gotten a
          -- type error before getting to this point.
          -- Ulf, 2019-11-21: Also @tactic clauses.
          cl <- inferMissingClause f sc
          return $ CoverResult (SplittingDone (size tel)) empty [] [cl] empty
        else do
          let ps' = fromSplitPatterns ps
          return $ CoverResult (SplittingDone (size tel)) empty [(tel, ps')] [] empty

    -- We need to split!
    -- If all clauses have an unsplit copattern, we try that first.
    Block res bs -> trySplitRes res (null bs) splitError $ do
      when (null bs) __IMPOSSIBLE__
      -- Otherwise, if there are variables to split, we try them
      -- in the order determined by a split strategy.
      reportSLn "tc.cover.strategy" 20 $ "blocking vars = " ++ prettyShow bs
      -- xs is a non-empty lists of blocking variables
      -- try splitting on one of them
      xs <- splitStrategy bs tel
      -- Andreas, 2017-10-08, issue #2594
      -- First, try to find split order for complete coverage.
      -- If this fails, try to at least carry out the splitting to the end.
      continue xs NoAllowPartialCover $ \ _err -> do
        continue xs YesAllowPartialCover $ \ err -> do
          splitError err
  where
    -- Andreas, 2019-08-07, issue #3966
    -- When we get a SplitError, tighten the error Range to the clauses
    -- that are still candidates for covering the SplitClause.
    splitError :: SplitError -> TCM a
    splitError = withRangeOfCandidateClauses . typeError . SplitError

    -- This repeats the matching, but since we are crashing anyway,
    -- the extra work just to compute a better Range does not matter.
    withRangeOfCandidateClauses :: TCM a -> TCM a
    withRangeOfCandidateClauses cont = do
      cands <- mapMaybe (uncurry notNo) . zip cs <$> mapM (matchClause ps) cs
      setCurrentRange cands cont
      where
        notNo :: Clause -> Match a -> Maybe Clause
        notNo c = \case
          Yes{}   -> Just c
          Block{} -> Just c
          No{}    -> Nothing

    -- Rename the variables in a telescope in accordance with their
    -- first appearance in the given NAPs. This is done to preserve
    -- variable names in IApplyConfluence error messages. Specifically,
    -- consider e.g.
    --
    --  data T : Set where
    --    x : T
    --    p : Path (Path T x x) refl refl
    --  f (p i j) = ...
    --
    -- When generating the covering clause corresponding to f's clause,
    -- the names we have in scope are i and i₁, since those are the
    -- names of both PathP binder arguments. (recall Path A x y = PathP (λ i → A) x y)
    -- So if we tried to print (Var 0 []) in the context of
    -- IApplyConfluence for that clause, what we see isn't j, it's i₁.
    --
    -- This function takes "name suggestions" from both variable
    -- patterns and IApply co/patterns, and replaces any existing names
    -- in the telescope by the name in that pattern.
    renTeleFromNap :: Telescope -> NAPs -> Telescope
    renTeleFromNap tel ps = telFromList $ evalState (traverse upd (telToList tel)) (size - 1)
      where
        -- Fold a single pattern into a map of name suggestions:
        -- In the running example above, we have
        --    f (p i@1 j@0)
        -- so the map that nameSuggest (p ...) returns is {0 → j, 1 → j}
        nameSuggest :: DeBruijnPattern -> IntMap ArgName
        nameSuggest ps = flip foldPattern ps $ \case
          VarP _ i | dbPatVarName i /= "_" ->
            IntMap.singleton (dbPatVarIndex i) (dbPatVarName i)
          IApplyP _ _ _ i | dbPatVarName i /= "_" ->
            IntMap.singleton (dbPatVarIndex i) (dbPatVarName i)
          _ -> mempty

        -- Suggestions from all patterns..
        suggestions = foldMap (nameSuggest . namedThing . unArg) ps

        -- The state will start counting from (length Γ - 1), which is
        -- the *highest* variable index, i.e. the index of the variable
        -- with level 0. Instead of doing a lot of de Bruijn arithmetic
        -- + recursion, traverse handles iteration and the State handles
        -- counting down.
        size = length (telToList tel)
        upd :: Dom (ArgName , Type) -> State Int (Dom (ArgName , Type))
        upd dom = state $ \s -> do
          case IntMap.lookup s suggestions of
            Just nm' -> ( dom{ domName = Just (WithOrigin CaseSplit (unranged nm'))
                             , unDom = (nm' , snd (unDom dom))
                             } , s - 1)
            Nothing -> (dom , s - 1)

    applyCl :: SplitClause -> Clause -> [(Nat, SplitPattern)] -> TCM Clause
    applyCl SClause{scTel = pretel, scPats = sps} cl mps
        | tel <- renTeleFromNap pretel (namedClausePats cl) = addContext tel $ do
        let ps = namedClausePats cl
        reportSDoc "tc.cover.applyCl" 40 $ "applyCl"
        reportSDoc "tc.cover.applyCl" 40 $ "tel    =" <+> pretty tel
        reportSDoc "tc.cover.applyCl" 40 $ "ps     =" <+> pretty ps
        reportSDoc "tc.cover.applyCl" 40 $ "mps    =" <+> pretty mps
        reportSDoc "tc.cover.applyCl" 40 $ "s      =" <+> pretty s
        reportSDoc "tc.cover.applyCl" 40 $ "ps[s]  =" <+> pretty (s `applySubst` ps)

        -- If a matching clause has fewer patterns than the split
        -- clause we ought to copy over the extra ones.
        -- e.g. if the user wrote:
        --
        --   bar : Bool -> Bool
        --   bar false = false
        --   bar = \ _ -> true
        --
        -- then for the second clause the @extra@ patterns will be @[true]@.

        let extra = drop (length ps) $ fromSplitPatterns sps
            n_extra = length extra

        reportSDoc "tc.cover.applyCl" 40 $ "extra  =" <+> pretty extra

        -- When we add the extra patterns we also update the type
        -- and the body of the clause.

        mtv <- (traverse . traverse) (telViewUpToPath n_extra) $ clauseType cl
        let ty = (fmap . fmap) ((parallelS (reverse $ map namedArg extra) `composeS` liftS n_extra s `applyPatSubst`) . theCore) mtv

        reportSDoc "tc.cover.applyCl" 40 $ "new ty =" <+> pretty ty

        return $
             Clause { clauseLHSRange  = clauseLHSRange cl
                    , clauseFullRange = clauseFullRange cl
                    , clauseTel       = tel
                    , namedClausePats = (s `applySubst` ps) ++ extra
                    , clauseBody      = (`applyE` patternsToElims extra) . (s `applyPatSubst`) <$> clauseBody cl
                    , clauseType      = ty
                    , clauseCatchall    = clauseCatchall cl
                    , clauseExact       = clauseExact cl
                    , clauseRecursive   = clauseRecursive cl
                    , clauseUnreachable = clauseUnreachable cl
                    , clauseEllipsis    = clauseEllipsis cl
                    , clauseWhereModule = clauseWhereModule cl
                    }
      where
      mps' =
        Map.fromList $
        map (mapSnd (namedArg . fromSplitPattern . defaultNamedArg)) mps
      s = parallelS (for (case Map.lookupMax mps' of
                            Nothing     -> []
                            Just (i, _) -> [0..i]) $ \ i ->
                     fromMaybe (deBruijnVar i) (Map.lookup i mps'))

    updateRelevance :: TCM a -> TCM a
    updateRelevance cont =
      -- Don't do anything if there is no target type info.
      caseMaybe target cont $ \ b -> do
        -- TODO (2018-10-16): if proofs get erased in the compiler, also wake erased vars!
        let m = getModality b
        applyModalityToContext m cont

    continue
      :: [BlockingVar]
      -> AllowPartialCover
      -> (SplitError -> TCM CoverResult)
      -> TCM CoverResult
    continue xs allowPartialCover handle = do
      r <- altM1 (\ x -> fmap (,x) <$> split Inductive allowPartialCover sc x) xs
      case r of
        Left err -> handle err
        -- If we get the empty covering, we have reached an impossible case
        -- and are done.
        Right (Covering n [], _) ->
         do
          -- TODO Andrea: I guess an empty pattern is not part of the cover?
          let qs = []
          return $ CoverResult (SplittingDone (size tel)) empty [] qs empty
        Right (Covering n scs', x) -> do
          let scs = map (\(t,(sc,i)) -> (t,sc)) scs'

          (results_trX, cs) <- createMissingIndexedClauses f n x sc scs' cs
          (scs, cs, results_hc) <- do
            let fallback = return (scs, cs, [])
            caseMaybeM (getPrimitiveName' builtinHComp) fallback $ \ comp -> do
            let isComp = \case
                  SplitCon c -> comp == c
                  _ -> False
            caseMaybe (List.find (isComp . fst) scs) fallback $ \ (sp, newSc) -> do
            (res,cs') <- createMissingHCompClause f n x sc newSc cs
            let scs2 = filter (not . isComp . fst) scs
            return (scs2,cs',res)
          let results_extra = results_hc ++ results_trX
              trees_extra = map (\(sp,cr) -> (sp, coverSplitTree cr)) results_extra

          results <- (++ map snd (results_extra)) <$> mapM ((cover f cs) . snd) scs
          let trees = map coverSplitTree      results
              useds = map coverUsedClauses    results
              psss  = map coverMissingClauses results
              qsss  = map coverPatterns       results
              noex  = map coverNoExactClauses results
          -- Jesper, 2016-03-10  We need to remember which variables were
          -- eta-expanded by the unifier in order to generate a correct split
          -- tree (see Issue 1872).
          reportSDoc "tc.cover.split.eta" 60 $ vcat
            [ "etaRecordSplits"
            , nest 2 $ vcat
              [ "n   = " <+> text (show n)
              , "scs = " <+> prettyTCM scs
              , "ps  = " <+> prettyTCMPatternList (fromSplitPatterns ps)
              ]
            ]
          let trees' = zipWith (etaRecordSplits (unArg n) ps) scs trees
              tree   = SplitAt n StrictSplit (trees' ++ trees_extra) -- TODO: Lazy?
          return $ CoverResult tree (IntSet.unions useds) (concat psss) (concat qsss) (IntSet.unions noex)

    -- Try to split result
    trySplitRes
      :: BlockedOnResult                  -- Are we blocked on the result?
      -> Bool                             -- Is this the last thing we try?
      -> (SplitError -> TCM CoverResult)  -- Handler for 'SplitError'
      -> TCM CoverResult                  -- Continuation
      -> TCM CoverResult
    -- not blocked on result: try regular splits
    trySplitRes NotBlockedOnResult finalSplit splitError cont
      | finalSplit = __IMPOSSIBLE__ -- there must be *some* reason we are blocked
      | otherwise  = cont
    -- blocked on arguments that are not yet introduced:

    -- we must split on a variable so that the target type becomes a pi type
    trySplitRes (BlockedOnApply IsApply) finalSplit splitError cont = do
      -- Andreas, 2021-12-31, issue #5712.
      -- If there is a tactic to solve the clause, we might not have inserted
      -- trailing args (due to #5358).  Now we force it!
      (tel, sc') <- insertTrailingArgs True sc
      if null tel then
        if finalSplit then __IMPOSSIBLE__ -- already ruled out by lhs checker
        else cont
      else cover f cs sc'

    -- ...or it was an IApply pattern, so we might just need to introduce the variable now.
    trySplitRes (BlockedOnApply IsIApply) finalSplit splitError cont
       = do
         caseMaybeM (splitResultPath f sc) fallback $ (cover f cs . snd) <=< insertTrailingArgs False
      where
        fallback | finalSplit = __IMPOSSIBLE__ -- already ruled out by lhs checker?
                 | otherwise  = cont

    -- blocked on result but there are catchalls:
    -- try regular splits if there are any, or else throw an error,
    -- this is nicer than continuing and reporting unreachable clauses
    -- (see issue #2833)
    trySplitRes (BlockedOnProj True) finalSplit splitError cont
      | finalSplit = splitError CosplitCatchall
      | otherwise  = cont
    -- all clauses have an unsplit copattern: try to split
    trySplitRes (BlockedOnProj False) finalSplit splitError cont = do
      reportSLn "tc.cover" 20 $ "blocked by projection pattern"
      -- forM is a monadic map over a Maybe here
      mcov <- splitResultRecord f sc
      case mcov of
        Left err
          | finalSplit -> splitError err
          | otherwise  -> cont
        Right (Covering n scs) -> do
          -- If result splitting was successful, continue coverage checking.
          (projs, results) <- unzip <$> do
            mapM (traverseF $ cover f cs <=< (snd <.> insertTrailingArgs False)) (map (\(t,(sc,i)) -> (t,sc)) scs)
            -- OR:
            -- forM scs $ \ (proj, sc') -> (proj,) <$> do
            --   cover f cs =<< do
            --     snd <$> fixTarget sc'
          let trees = map coverSplitTree results
              useds = map coverUsedClauses results
              psss  = map coverMissingClauses results
              qsss  = map coverPatterns results
              noex  = map coverNoExactClauses results
              tree  = SplitAt n StrictSplit $ zip projs trees   -- TODO: Lazy?
          return $ CoverResult tree (IntSet.unions useds) (concat psss) (concat qsss) (IntSet.unions noex)

    gatherEtaSplits :: Int -> SplitClause
                    -> [NamedArg SplitPattern] -> [NamedArg SplitPattern]
    gatherEtaSplits n sc []
       | n >= 0    = __IMPOSSIBLE__ -- we should have encountered the main
                                    -- split by now already
       | otherwise = []
    gatherEtaSplits n sc (p:ps) = case namedArg p of
      VarP _ x
       | n == 0    -> case p' of -- this is the main split
           VarP  _ _    -> p : gatherEtaSplits (-1) sc ps
           DotP  _ _    -> __IMPOSSIBLE__
           ConP  _ _ qs -> qs ++ gatherEtaSplits (-1) sc ps
           LitP{}       -> gatherEtaSplits (-1) sc ps
           ProjP{}      -> __IMPOSSIBLE__
           IApplyP{}    -> __IMPOSSIBLE__
           DefP  _ _ qs -> qs ++ gatherEtaSplits (-1) sc ps -- __IMPOSSIBLE__ -- Andrea: maybe?
       | otherwise ->
           updateNamedArg (\ _ -> p') p : gatherEtaSplits (n-1) sc ps
        where p' = lookupS (scSubst sc) $ splitPatVarIndex x
      IApplyP{}   ->
           updateNamedArg (applySubst (scSubst sc)) p : gatherEtaSplits (n-1) sc ps
      DotP  _ _    -> p : gatherEtaSplits (n-1) sc ps -- count dot patterns
      ConP  _ _ qs -> gatherEtaSplits n sc (qs ++ ps)
      DefP  _ _ qs -> gatherEtaSplits n sc (qs ++ ps)
      LitP{}       -> gatherEtaSplits n sc ps
      ProjP{}      -> gatherEtaSplits n sc ps

    addEtaSplits :: Int -> [NamedArg SplitPattern] -> SplitTree -> SplitTree
    addEtaSplits k []     t = t
    addEtaSplits k (p:ps) t = case namedArg p of
      VarP  _ _     -> addEtaSplits (k+1) ps t
      DotP  _ _     -> addEtaSplits (k+1) ps t
      ConP c cpi qs -> SplitAt (p $> k) LazySplit [(SplitCon (conName c) , addEtaSplits k (qs ++ ps) t)]
      LitP{}        -> __IMPOSSIBLE__
      ProjP{}       -> __IMPOSSIBLE__
      DefP{}        -> __IMPOSSIBLE__ -- Andrea: maybe?
      IApplyP{}     -> addEtaSplits (k+1) ps t

    etaRecordSplits :: Int -> [NamedArg SplitPattern] -> (SplitTag,SplitClause)
                    -> SplitTree -> (SplitTag,SplitTree)
    etaRecordSplits n ps (q , sc) t =
      (q , addEtaSplits 0 (gatherEtaSplits n sc ps) t)


-- | Append a instance clause to the clauses of a function.
inferMissingClause
  :: QName
       -- ^ Function name.
  -> SplitClause
       -- ^ Clause to add.  Clause hiding (in 'clauseType') must be 'Instance'.
   -> TCM Clause
inferMissingClause f (SClause tel ps _ cps (Just t)) = setCurrentRange f $ do
  reportSDoc "tc.cover.infer" 20 $ addContext tel $ "Trying to infer right-hand side of type" <+> prettyTCM t
  rhs <-
    addContext tel
    $ locallyTC eCheckpoints (const cps)
    $ checkpoint IdS    -- introduce a fresh checkpoint
    $ case getHiding t of
        _ | Just tac <- domTactic t -> do
          reportSDoc "tc.cover.infer" 40 $ vcat
            [ "@tactic rhs"
            , nest 2 $ "target =" <+> pretty t ]
          (_, v) <- newValueMeta DontRunMetaOccursCheck CmpLeq (unDom t)
          v <$ unquoteTactic tac v (unDom t)
        Instance{} -> snd <$> newInstanceMeta "" (unDom t)
        Hidden     -> __IMPOSSIBLE__
        NotHidden  -> __IMPOSSIBLE__
  let cl = Clause { clauseLHSRange  = noRange
                  , clauseFullRange = noRange
                  , clauseTel       = tel
                  , namedClausePats = fromSplitPatterns ps
                  , clauseBody      = Just rhs
                  , clauseType      = Just (argFromDom t)
                  , clauseCatchall    = False
                  , clauseExact       = Just True
                  , clauseRecursive   = Nothing     -- could be recursive
                  , clauseUnreachable = Just False  -- missing, thus, not unreachable
                  , clauseEllipsis    = NoEllipsis
                  , clauseWhereModule = Nothing
                  }
  addClauses f [cl]  -- Important: add at the end.
  return cl
inferMissingClause _ (SClause _ _ _ _ Nothing) = __IMPOSSIBLE__

splitStrategy :: BlockingVars -> Telescope -> TCM BlockingVars
splitStrategy bs tel = return $ updateLast setBlockingVarOverlap xs
  -- Make sure we do not insists on precomputed coverage when
  -- we make our last try to split.
  -- Otherwise, we will not get a nice error message.
  where
    xs             = strict ++ lazy
    (lazy, strict) = List.partition blockingVarLazy bs
{- KEEP!
--  Andreas, 2012-10-13
--  The following split strategy which prefers all-constructor columns
--  fails on test/fail/CoverStrategy
    xs       = ys ++ zs
    (ys, zs) = partition allConstructors bs
    allConstructors :: BlockingVar -> Bool
    allConstructors = isJust . snd
-}


-- | Check that a type is a non-irrelevant datatype or a record with
-- named constructor. Unless the 'Induction' argument is 'CoInductive'
-- the data type must be inductive.
isDatatype :: (MonadTCM tcm, MonadError SplitError tcm) =>
              Induction -> Dom Type ->
              tcm (DataOrRecord, QName, [Arg Term], [Arg Term], [QName], Bool)
isDatatype ind at = do
  let t       = unDom at
      throw f = throwError . f =<< do liftTCM $ buildClosure t
  t' <- liftTCM $ reduce t
  mInterval <- liftTCM $ getBuiltinName' builtinInterval
  mIsOne <- liftTCM $ getBuiltinName' builtinIsOne
  case unEl t' of
    Def d [] | Just d == mInterval -> throw NotADatatype
    Def d [Apply phi] | Just d == mIsOne -> do
                xs <- liftTCM $ decomposeInterval =<< reduce (unArg phi)
                if null xs
                   then return $ (IsData, d, [phi], [], [], False)
                   else throw NotADatatype
    Def d es -> do
      let ~(Just args) = allApplyElims es
      def <- liftTCM $ theDef <$> getConstInfo d
      case def of
        Datatype{dataPars = np, dataCons = cs}
          | otherwise -> do
              let (ps, is) = splitAt np args
              return (IsData, d, ps, is, cs, not $ null (dataPathCons def))
        Record{recPars = np, recConHead = con, recInduction = i, recEtaEquality'}
          | i == Just CoInductive && ind /= CoInductive ->
              throw CoinductiveDatatype
          | otherwise ->
              return (IsRecord i recEtaEquality', d, args, [], [conName con], False)
        _ -> throw NotADatatype
    _ -> throw NotADatatype

-- | Update the target type of the split clause after a case split.
fixTargetType
  :: Quantity  -- ^ The quantity of the thing that is split.
  -> SplitTag -> SplitClause -> Dom Type -> TCM SplitClause
fixTargetType q tag sc@SClause{ scTel = sctel, scSubst = sigma } target = do
    reportSDoc "tc.cover.target" 20 $ sep
      [ "split clause telescope: " <+> prettyTCM sctel
      ]
    reportSDoc "tc.cover.target" 60 $ sep
      [ "substitution          : " <+> prettyTCM sigma
      ]
    reportSDoc "tc.cover.target" 60 $ sep
      [ "target type before substitution:" <+> pretty target
      , "             after substitution:" <+> pretty (applySplitPSubst sigma target)
      ]

    -- We update the target quantity to 0 for erased constructors, but
    -- not if the match is made in an erased position, or if the
    -- original constructor definition is not erased.
    updQuant <- do
      let erased = case q of
            Quantity0{} -> True
            Quantity1{} -> __IMPOSSIBLE__
            Quantityω{} -> False
      if erased then return id else case tag of
        SplitCon c -> do
          q <- getQuantity <$> getOriginalConstInfo c
          case q of
            Quantity0{} -> return $ mapQuantity (composeQuantity q)
            Quantity1{} -> return id
            Quantityω{} -> return id
        SplitLit{} -> return id
        SplitCatchall{} -> return id

    return $ sc { scTarget = Just $ updQuant $ applySplitPSubst sigma target }


-- | Add more patterns to split clause if the target type is a function type.
--   Returns the domains of the function type (if any).
insertTrailingArgs
  :: Bool         -- ^ Force insertion even when there is a 'domTactic'?
  -> SplitClause
  -> TCM (Telescope, SplitClause)
insertTrailingArgs force sc@SClause{ scTel = sctel, scPats = ps, scSubst = sigma, scCheckpoints = cps, scTarget = target } = do
  let fallback = return (empty, sc)
  caseMaybe target fallback $ \ a -> do
    if isJust (domTactic a) && not force then fallback else do
    (TelV tel b) <- addContext sctel $ telViewUpTo (-1) $ unDom a
    reportSDoc "tc.cover.target" 15 $ sep
      [ "target type telescope: " <+> do
          addContext sctel $ prettyTCM tel
      , "target type core     : " <+> do
          addContext sctel $ addContext tel $ prettyTCM b
      ]
    let n         = size tel
        -- Andreas, 2016-10-04 issue #2236
        -- Need to set origin to "Inserted" to avoid printing of hidden patterns.
        xs        = map (mapArgInfo hiddenInserted) $ teleNamedArgs tel
        -- Compute new split clause
        sctel'    = telFromList $ telToList (raise n sctel) ++ telToList tel
        -- Dot patterns in @ps@ need to be raised!  (Issue 1298)
        ps'       = applySubst (raiseS n) ps ++ xs
        newTarget = Just $ (if not (null tel) then a{ domTactic = Nothing } else a) $> b
        sc'       = SClause
          { scTel    = sctel'
          , scPats   = ps'
          , scSubst  = wkS n $ sigma -- Should be wkS instead of liftS since
                                     -- variables are only added to new tel.
          , scCheckpoints        = applySubst (raiseS n) cps
          , scTarget = newTarget
          }
    -- Separate debug printing to find cause of crash (Issue 1374)
    reportSDoc "tc.cover.target" 30 $ sep
      [ "new split clause telescope   : " <+> prettyTCM sctel'
      ]
    reportSDoc "tc.cover.target" 30 $ sep
      [ "new split clause patterns    : " <+> do
          addContext sctel' $ prettyTCMPatternList $ fromSplitPatterns ps'
      ]
    reportSDoc "tc.cover.target" 60 $ sep
      [ "new split clause substitution: " <+> prettyTCM (scSubst sc')
      ]
    reportSDoc "tc.cover.target" 30 $ sep
      [ "new split clause target      : " <+> do
          addContext sctel' $ prettyTCM $ fromJust newTarget
      ]
    reportSDoc "tc.cover.target" 20 $ sep
      [ "new split clause"
      , prettyTCM sc'
      ]
    return $ if n == 0 then (empty, sc { scTarget = newTarget }) else (tel, sc')

-- Andreas, 2017-01-18, issue #819, set visible arguments to UserWritten.
-- Otherwise, they will be printed as _.
hiddenInserted :: ArgInfo -> ArgInfo
hiddenInserted ai
  | visible ai = setOrigin UserWritten ai
  | otherwise  = setOrigin Inserted ai


-- | Checks if a type in this sort supports hcomp.
--   currently all such types will have a Level.
--   precondition: Sort in whnf and not blocked.
hasHComp :: Sort -> Maybe Level
hasHComp (Type l) = Just l
hasHComp _        = Nothing


computeHCompSplit  :: Telescope   -- ^ Telescope before split point.
  -> PatVarName                   -- ^ Name of pattern variable at split point.
  -> Telescope                    -- ^ Telescope after split point.
  -> QName                        -- ^ Name of datatype to split at.
  -> Args                         -- ^ Data type parameters.
  -> Args                         -- ^ Data type indices.
  -> Nat                          -- ^ Index of split variable.
  -> Telescope                    -- ^ Telescope for the patterns.
  -> [NamedArg SplitPattern]      -- ^ Patterns before doing the split.
  -> Map CheckpointId Substitution -- ^ Current checkpoints
  -- -> QName                        -- ^ Constructor to fit into hole.
  -> CoverM (Maybe (SplitTag,SplitClause))   -- ^ New split clause if successful.
computeHCompSplit delta1 n delta2 d pars ixs hix tel ps cps = do
  withK   <- not . collapseDefault . optCubicalCompatible <$> pragmaOptions
  if withK then return Nothing else do
    -- Get the type of the datatype
  -- Δ1 ⊢ dtype
  dsort <- liftTCM $ (parallelS (reverse $ map unArg pars) `applySubst`) . dataSort . theDef <$> getConstInfo d
  hCompName <- fromMaybe __IMPOSSIBLE__ <$> getPrimitiveName' builtinHComp
  theHCompT <- defType <$> getConstInfo hCompName

  -- TODO can dsort be blocked or not in whnf?
  caseMaybe (hasHComp dsort) (return Nothing) $ \ dlvl' -> do
  let
    dlvl = Level dlvl'
    dterm = Def d [] `apply` (pars ++ ixs)
  -- Δ1 ⊢ gamma
  TelV gamma _ <- lift $ telView (theHCompT `piApply` [setHiding Hidden $ defaultArg $ dlvl , defaultArg $ dterm])
  case (delta1 `abstract` gamma,IdS) of
    (delta1',rho0) -> do
--      debugSubst "rho0" rho0

      -- We have Δ₁' ⊢ ρ₀ : Δ₁Γ, so split it into the part for Δ₁ and the part for Γ
      let (rho1,rho2) = splitS (size gamma) $ toSplitPSubst rho0

      let defp = DefP defaultPatternInfo hCompName . map (setOrigin Inserted) $ -- should there be a different Origin here?
                   map (fmap unnamed) [setHiding Hidden $ defaultArg $ applySubst rho1 $ DotP defaultPatternInfo $ dlvl
                                      ,setHiding Hidden $ defaultArg $ applySubst rho1 $ DotP defaultPatternInfo $ dterm]
                   ++ applySubst rho2 (teleNamedArgs gamma) -- rho0?
      -- Compute final context and substitution
      let rho3    = consS defp rho1            -- Δ₁' ⊢ ρ₃ : Δ₁(x:D)
          delta2' = applySplitPSubst rho3 delta2  -- Δ₂' = Δ₂ρ₃
          delta'  = delta1' `abstract` delta2' -- Δ'  = Δ₁'Δ₂'
          rho     = liftS (size delta2) rho3   -- Δ' ⊢ ρ : Δ₁(x:D)Δ₂

      -- debugTel "delta'" delta'
      -- debugSubst "rho" rho
      -- debugPs tel ps

      -- Apply the substitution
      let ps' = applySubst rho ps
      -- debugPlugged delta' ps'

      let cps' = applySplitPSubst rho cps

      return $ Just . (SplitCon hCompName,) $ SClause delta' ps' rho cps' Nothing -- target fixed later


-- | @computeNeighbourhood delta1 delta2 d pars ixs hix tel ps con@
--
--   @
--      delta1   Telescope before split point
--      n        Name of pattern variable at split point
--      delta2   Telescope after split point
--      d        Name of datatype to split at
--      pars     Data type parameters
--      ixs      Data type indices
--      hix      Index of split variable
--      tel      Telescope for patterns ps
--      ps       Patterns before doing the split
--      cps      Current module parameter checkpoints
--      con      Constructor to fit into hole
--   @
--   @dtype == d pars ixs@
computeNeighbourhood
  :: Telescope                    -- ^ Telescope before split point.
  -> PatVarName                   -- ^ Name of pattern variable at split point.
  -> Telescope                    -- ^ Telescope after split point.
  -> QName                        -- ^ Name of datatype to split at.
  -> Args                         -- ^ Data type parameters.
  -> Args                         -- ^ Data type indices.
  -> Nat                          -- ^ Index of split variable.
  -> Telescope                    -- ^ Telescope for the patterns.
  -> [NamedArg SplitPattern]      -- ^ Patterns before doing the split.
  -> Map CheckpointId Substitution -- ^ Current checkpoints
  -> QName                        -- ^ Constructor to fit into hole.
  -> CoverM (Maybe (SplitClause, IInfo))   -- ^ New split clause if successful.
computeNeighbourhood delta1 n delta2 d pars ixs hix tel ps cps c = do

  -- Get the type of the datatype
  dtype <- liftTCM $ (`piApply` pars) . defType <$> getConstInfo d

  -- Get the real constructor name
  con <- liftTCM $ fromRight __IMPOSSIBLE__ <$> getConForm c
  con <- return $ con { conName = c }  -- What if we restore the current name?
                                       -- Andreas, 2013-11-29 changes nothing!

  -- Get the type of the constructor
  ctype <- liftTCM $ defType <$> getConInfo con

  -- Lookup the type of the constructor at the given parameters
  (gamma0, cixs, boundary) <- do
    (TelV gamma0 (El _ d), boundary) <- liftTCM $ addContext delta1 $
      telViewPathBoundaryP (ctype `piApply` pars)
    let Def _ es = d
        Just cixs = allApplyElims es
    return (gamma0, cixs, boundary)

  let (_, Dom{domInfo = info} : _) = splitAt (size tel - hix - 1) (telToList tel)

  -- Andreas, 2012-02-25 preserve name suggestion for recursive arguments
  -- of constructor

  let preserve (x, t@(El _ (Def d' _))) | d == d' = (n, t)
      preserve (x, t) = (x, t)
      gamma  = (fmap . mapModality) (composeModality (getModality info)) $ telFromList . map (fmap preserve) . telToList $ gamma0
      delta1Gamma = delta1 `abstract` gamma

  debugInit con ctype d pars ixs cixs delta1 delta2 gamma tel ps hix

  cforced <- defForced <$> getConstInfo c
      -- Variables in Δ₁ are not forced, since the unifier takes care to not introduce forced
      -- variables.
  let forced = replicate (size delta1) NotForced ++ cforced
      flex   = allFlexVars forced delta1Gamma -- All variables are flexible

  -- Unify constructor target and given type (in Δ₁Γ)
  let conIxs   = drop (size pars) cixs
      givenIxs = raise (size gamma) ixs

  -- Andrea 2019-07-17 propagate the Cohesion to the equation telescope
  -- TODO: should we propagate the modality in general?
  -- See also LHS checking.
  dtype <- addContext delta1 $ do
         let updCoh = composeCohesion (getCohesion info)
         TelV dtel dt <- telView dtype
         return $ abstract (mapCohesion updCoh <$> dtel) dt
  dsort <- addContext delta1 $ reduce (getSort dtype)

  withKIfStrict <- case dsort of
    SSet{} -> return $ locallyTC eSplitOnStrict $ const True
    _      -> return id

  -- Should we attempt to compute a left inverse for this clause? When
  -- --cubical-compatible --flat-split is given, we don't generate a
  -- left inverse (at all). This means that, when the coverage checker
  -- gets to the clause this was in, it won't generate a (malformed!)
  -- transpX clause for @♭ matching.
  -- TODO(Amy): properly support transpX when @♭ stuff is in the
  -- context.
  let flatSplit = boolToMaybe (getCohesion info == Flat) SplitOnFlat

  r <- withKIfStrict $ lift $ unifyIndices' flatSplit
         delta1Gamma
         flex
         (raise (size gamma) dtype)
         conIxs
         givenIxs

  TelV eqTel _ <- telView $ (raise (size gamma) dtype)

  let stuck b errs = do
        debugCantSplit
        throwError $ UnificationStuck b (conName con) (delta1 `abstract` gamma) conIxs givenIxs errs


  case r of
    NoUnify {} -> debugNoUnify $> Nothing

    UnifyBlocked block -> stuck (Just block) []

    UnifyStuck errs -> stuck Nothing errs

    Unifies (delta1',rho0,eqs,tauInv) -> do

      let unifyInfo | Type _ <- dsort     -- only types of sort Type l have trX constructors:
                                          -- re #3733: update if we add transp for other sorts.
                    , not $ null $ conIxs -- no point propagating this info if trivial?
                    , Right (tau,leftInv) <- tauInv
            = TheInfo $ UE delta1Gamma delta1' eqTel (map unArg conIxs) (map unArg givenIxs) rho0 tau leftInv
                    | otherwise
            = NoInfo

      case tauInv of
        Right{} -> return ()
        Left SplitOnStrict -> return ()
        Left x -> do
          whenM (collapseDefault . optCubicalCompatible <$>
                 pragmaOptions) $ do
            -- re #3733: TODO better error msg.
            lift $ warning . UnsupportedIndexedMatch =<< prettyTCM x

      debugSubst "rho0" rho0

      let rho0' = toSplitPSubst rho0

      -- We have Δ₁' ⊢ ρ₀ : Δ₁Γ, so split it into the part for Δ₁ and the part for Γ
      let (rho1,rho2) = splitS (size gamma) $ rho0'

      -- Andreas, 2015-05-01  I guess it is fine to use no @conPType@
      -- as the result of splitting is never used further down the pipeline.
      -- After splitting, Agda reloads the file.
      -- Andreas, 2017-09-03, issue #2729: remember that pattern was generated by case split.
      let cpi  = noConPatternInfo{ conPInfo = PatternInfo PatOSplit [] , conPRecord = True }
          conp = ConP con cpi $ applySubst rho0' $
                   map (mapArgInfo hiddenInserted) $ telePatterns' (tele2NamedArgs gamma0) gamma boundary
          -- Andreas, 2016-09-08, issue #2166: use gamma0 for correct argument names

      -- Compute final context and substitution
      let rho3    = consS conp rho1            -- Δ₁' ⊢ ρ₃ : Δ₁(x:D)
          delta2' = applySplitPSubst rho3 delta2  -- Δ₂' = Δ₂ρ₃
          delta'  = delta1' `abstract` delta2' -- Δ'  = Δ₁'Δ₂'
          rho     = liftS (size delta2) rho3   -- Δ' ⊢ ρ : Δ₁(x:D)Δ₂

      debugTel "delta'" delta'
      debugSubst "rho" rho
      debugPs tel ps

      -- Apply the substitution
      let ps' = applySubst rho ps
      debugPlugged delta' ps'

      let cps'  = applySplitPSubst rho cps

      return $ Just . (,unifyInfo) $ SClause delta' ps' rho cps' Nothing -- target fixed later

  where
    debugInit con ctype d pars ixs cixs delta1 delta2 gamma tel ps hix = liftTCM $ do
      reportSDoc "tc.cover.split.con" 20 $ vcat
        [ "computeNeighbourhood"
        , nest 2 $ vcat
          [ "context=" <+> (inTopContext . prettyTCM =<< getContextTelescope)
          , "con    =" <+> prettyTCM con
          , "ctype  =" <+> prettyTCM ctype
          , "ps     =" <+> do inTopContext $ addContext tel $ prettyTCMPatternList $ fromSplitPatterns ps
          , "d      =" <+> prettyTCM d
          , "pars   =" <+> do prettyList $ map prettyTCM pars
          , "ixs    =" <+> do addContext delta1 $ prettyList $ map prettyTCM ixs
          , "cixs   =" <+> do addContext gamma  $ prettyList $ map prettyTCM cixs
          , "delta1 =" <+> do inTopContext $ prettyTCM delta1
          , "delta2 =" <+> do inTopContext $ addContext delta1 $ addContext n $ prettyTCM delta2
          , "gamma  =" <+> do inTopContext $ addContext delta1 $ prettyTCM gamma
          , "tel  =" <+> do inTopContext $ prettyTCM tel
          , "hix    =" <+> text (show hix)
          ]
        ]
      reportSDoc "tc.cover.split.con" 70 $ vcat
        [ "computeNeighbourhood"
        , nest 2 $ vcat
          [ "context=" <+> (inTopContext . (text . show) =<< getContextTelescope)
          , "con    =" <+> (text . show) con
          , "ctype  =" <+> (text . show) ctype
          , "ps     =" <+> (text . show) ps
          , "d      =" <+> (text . show) d
          , "pars   =" <+> (text . show) pars
          , "ixs    =" <+> (text . show) ixs
          , "cixs   =" <+> (text . show) cixs
          , "delta1 =" <+> (text . show) delta1
          , "delta2 =" <+> (text . show) delta2
          , "gamma  =" <+> (text . show) gamma
          , "hix    =" <+> text (show hix)
          ]
        ]

    debugNoUnify =
      liftTCM $ reportSLn "tc.cover.split.con" 20 "  Constructor impossible!"

    debugCantSplit =
      liftTCM $ reportSLn "tc.cover.split.con" 20 "  Bad split!"

    debugSubst s sub =
      liftTCM $ reportSDoc "tc.cover.split.con" 20 $ nest 2 $ vcat
        [ text (s ++ " =") <+> prettyTCM sub
        ]

    debugTel s tel =
      liftTCM $ reportSDoc "tc.cover.split.con" 20 $ nest 2 $ vcat
        [ text (s ++ " =") <+> prettyTCM tel
        ]

    debugPs tel ps =
      liftTCM $ reportSDoc "tc.cover.split.con" 20 $
        inTopContext $ addContext tel $ nest 2 $ vcat
          [ "ps     =" <+> prettyTCMPatternList (fromSplitPatterns ps)
          ]

    debugPlugged delta' ps' = do
      liftTCM $ reportSDoc "tc.cover.split.con" 20 $
        inTopContext $ addContext delta' $ nest 2 $ vcat
          [ "ps'    =" <+> do prettyTCMPatternList $ fromSplitPatterns ps'
          ]

-- | Introduce trailing pattern variables?
data InsertTrailing
  = DoInsertTrailing
  | DontInsertTrailing
  deriving (Eq, Show)

-- | Allow partial covering for split?
data AllowPartialCover
  = YesAllowPartialCover  -- To try to coverage-check incomplete splits.
  | NoAllowPartialCover   -- Default.
  deriving (Eq, Show)

-- | Entry point from @Interaction.MakeCase@.
splitClauseWithAbsurd :: SplitClause -> Nat -> TCM (Either SplitError (Either SplitClause Covering))
splitClauseWithAbsurd c x =
  split' CheckEmpty Inductive NoAllowPartialCover DontInsertTrailing c (BlockingVar x [] [] True False)
  -- Andreas, 2016-05-03, issue 1950:
  -- Do not introduce trailing pattern vars after split,
  -- because this does not work for with-clauses.

-- | Entry point from @TypeChecking.Empty@ and @Interaction.BasicOps@.
--   @splitLast CoInductive@ is used in the @refine@ tactics.

splitLast :: Induction -> Telescope -> [NamedArg DeBruijnPattern] -> TCM (Either SplitError Covering)
splitLast ind tel ps = split ind NoAllowPartialCover sc (BlockingVar 0 [] [] True False)
  where sc = SClause tel (toSplitPatterns ps) empty empty target
        -- TODO 2ltt: allows (Empty_fib -> Empty_strict) which is not conservative
        target = (Just $ defaultDom $ El (Prop (Max 0 [])) $ Dummy "splitLastTarget" [])

-- | @split ind splitClause x = return res@
--   splits @splitClause@ at pattern var @x@ (de Bruijn index).
--
--   Possible results @res@ are:
--
--   1. @Left err@:
--      Splitting failed.
--
--   2. @Right covering@:
--      A covering set of split clauses, one for each valid constructor.
--      This could be the empty set (denoting an absurd clause).

split :: Induction
         -- ^ Coinductive constructors are allowed if this argument is
         -- 'CoInductive'.
      -> AllowPartialCover
         -- ^ Don't fail if computed 'Covering' does not cover all constructors.
      -> SplitClause
      -> BlockingVar
      -> TCM (Either SplitError Covering)
split ind allowPartialCover sc x =
  fmap blendInAbsurdClause <$> split' NoCheckEmpty ind allowPartialCover DoInsertTrailing sc x
  where
    n = lookupPatternVar sc $ blockingVarNo x
    blendInAbsurdClause :: Either SplitClause Covering -> Covering
    blendInAbsurdClause = fromRight (const $ Covering n [])

-- | Convert a de Bruijn index relative to the clause telescope to a de Bruijn
--   level. The result should be the argument position (counted from left,
--   starting with 0) to split at (dot patterns included!).
lookupPatternVar :: SplitClause -> Int -> Arg Nat
lookupPatternVar SClause{ scTel = tel, scPats = pats } x = arg $>
    if n < 0 then __IMPOSSIBLE__ else n
  where n = if k < 0
            then __IMPOSSIBLE__
            else fromMaybe __IMPOSSIBLE__ $ permPicks perm !!! k
        perm = fromMaybe __IMPOSSIBLE__ $ dbPatPerm $ fromSplitPatterns pats
        k = size tel - x - 1
        arg = indexWithDefault __IMPOSSIBLE__ (telVars (size tel) tel) k


data CheckEmpty = CheckEmpty | NoCheckEmpty

-- | @split' ind pc ft splitClause x = return res@
--   splits @splitClause@ at pattern var @x@ (de Bruijn index).
--
--   Possible results @res@ are:
--
--   1. @Left err@:
--      Splitting failed.
--
--   2. @Right (Left splitClause')@:
--      Absurd clause (type of @x@ has 0 valid constructors).
--
--   3. @Right (Right covering)@:
--      A covering set of split clauses, one for each valid constructor.

split' :: CheckEmpty
          -- ^ Use isEmptyType to check whether the type of the variable to
          -- split on is empty. This switch is necessary to break the cycle
          -- between split' and isEmptyType.
       -> Induction
          -- ^ Coinductive constructors are allowed if this argument is
          -- 'CoInductive'.
       -> AllowPartialCover
          -- ^ Don't fail if computed 'Covering' does not cover all constructors.
       -> InsertTrailing
          -- ^ If 'DoInsertTrailing', introduce new trailing variable patterns.
       -> SplitClause
       -> BlockingVar
       -> TCM (Either SplitError (Either SplitClause Covering))
split' checkEmpty ind allowPartialCover inserttrailing
       sc@(SClause tel ps _ cps target) (BlockingVar x pcons' plits overlap lazy) =
 liftTCM $ runExceptT $ do
  debugInit tel x ps cps

  -- Split the telescope at the variable
  -- t = type of the variable,  Δ₁ ⊢ t
  (n, t, delta1, delta2) <- do
    let (tel1, dom : tel2) = splitAt (size tel - x - 1) $ telToList tel
    return (fst $ unDom dom, snd <$> dom, telFromList tel1, telFromList tel2)

  -- Compute the neighbourhoods for the constructors
  let computeNeighborhoods = do
        -- Check that t is a datatype or a record
        -- Andreas, 2010-09-21, isDatatype now directly throws an exception if it fails
        -- cons = constructors of this datatype
        (dr, d, pars, ixs, cons', isHIT) <- inContextOfT $ isDatatype ind t
        isFib <- lift $ isFibrant t
        cons <- case checkEmpty of
          CheckEmpty   -> ifM (liftTCM $ inContextOfT $ isEmptyType $ unDom t) (pure []) (pure cons')
          NoCheckEmpty -> pure cons'
        mns  <- forM cons $ \ con -> fmap (SplitCon con,) <$>
          computeNeighbourhood delta1 n delta2 d pars ixs x tel ps cps con
        hcompsc <- if isFib && (isHIT || (size ixs > 0)) && not (null mns) && inserttrailing == DoInsertTrailing
                   then computeHCompSplit delta1 n delta2 d pars ixs x tel ps cps
                   else return Nothing
        let ns = catMaybes mns
        return ( dr
               , not (null ixs) -- Is "d" indexed?
               , length $ ns
               , ns ++ catMaybes ([fmap (fmap (,NoInfo)) hcompsc | not $ null $ ns])
               )

      computeLitNeighborhoods = do
        typeOk <- liftTCM $ do
          t' <- litType $ headWithDefault {-'-} __IMPOSSIBLE__ plits
          liftTCM $ dontAssignMetas $ tryConversion $ equalType (unDom t) t'
        unless typeOk $ throwError . NotADatatype =<< do liftTCM $ buildClosure (unDom t)
        ns <- forM plits $ \lit -> do
          let delta2' = subst 0 (Lit lit) delta2
              delta'  = delta1 `abstract` delta2'
              rho     = liftS x $ consS (litP lit) idS
              ps'     = applySubst rho ps
              cps'    = applySplitPSubst rho cps
          return (SplitLit lit , SClause delta' ps' rho cps' Nothing)
        ca <- do
          let delta' = tel -- telescope is unchanged for catchall branch
              varp   = VarP (PatternInfo PatOSplit []) $ SplitPatVar
                         { splitPatVarName   = underscore
                         , splitPatVarIndex  = 0
                         , splitExcludedLits = plits
                         }
              rho    = liftS x $ consS varp $ raiseS 1
              ps'    = applySubst rho ps
          return (SplitCatchall , SClause delta' ps' rho cps Nothing)

        -- If Agda is changed so that the type of a literal can belong
        -- to an inductive family (with at least one index), then the
        -- following code should be changed (the constructor False
        -- stands for "not indexed").
        let ns' = map ((fmap (,NoInfo))) $ ns ++ [ ca ]
        return (IsData, False, length ns', ns')

  -- numMatching is the number of proper constructors matching, excluding hcomp.
  -- for literals this considers the catchall clause as 1 extra constructor.
  (dr, isIndexed, numMatching, ns) <- if null pcons' && not (null plits)
        then computeLitNeighborhoods
        else computeNeighborhoods

  ns <- case target of
    Just a  -> forM ns $ \ (con,(sc,info)) -> lift $ (con,) . (,info) <$>
                 fixTargetType (getQuantity t) con sc a
    Nothing -> return ns

  ns <- case inserttrailing of
    DontInsertTrailing -> return ns
    DoInsertTrailing   -> lift $ forM ns $ \(con,(sc,info)) ->
      (con,) . (,info) . snd <$> insertTrailingArgs False sc

  mHCompName <- getPrimitiveName' builtinHComp
  withoutK   <- collapseDefault . optWithoutK <$> pragmaOptions

  erased <- asksTC hasQuantity0
  reportSLn "tc.cover.split" 60 $ "We are in erased context = " ++ show erased
  let erasedError causedByWithoutK =
        throwError . ErasedDatatype causedByWithoutK =<<
          do liftTCM $ inContextOfT $ buildClosure (unDom t)

  case numMatching of
    0  -> do
      let absurdp = VarP (PatternInfo PatOAbsurd []) $ SplitPatVar underscore 0 []
          rho = liftS x $ consS absurdp $ raiseS 1
          ps' = applySubst rho ps
      return $ Left $ SClause
               { scTel  = tel
               , scPats = ps'
               , scSubst              = __IMPOSSIBLE__ -- not used
               , scCheckpoints        = __IMPOSSIBLE__ -- not used
               , scTarget             = Nothing
               }

    -- Andreas, 2018-10-17: If more than one constructor matches, we cannot erase.
    n | n > 1 && not erased && not (usableQuantity t) ->
      erasedError False

    -- If exactly one constructor matches and the K rule is turned
    -- off, then we only allow erasure for non-indexed data types
    -- (#4172).
    1 | not erased && not (usableQuantity t) &&
          withoutK && isIndexed ->
      erasedError True

    _ -> do

      -- Andreas, 2012-10-10 fail if precomputed constructor set does not cover
      -- all the data type constructors
      -- Andreas, 2017-10-08 ... unless partial covering is explicitly allowed.
      let ptags = map (SplitCon . conName) pcons' ++ map SplitLit plits
      -- clauses for hcomp will be automatically generated.
      let inferred_tags = maybe Set.empty (Set.singleton . SplitCon) mHCompName
      let all_tags = Set.fromList ptags `Set.union` inferred_tags

      when (allowPartialCover == NoAllowPartialCover && not overlap) $
        for_ ns $ \(tag, (sc, _)) -> do
          unless (tag `Set.member` all_tags) $ do
            isImpossibleClause <- liftTCM $ isEmptyTel $ scTel sc
            unless isImpossibleClause $ do
              liftTCM $ reportSDoc "tc.cover" 10 $ vcat
                [ text "Missing case for" <+> prettyTCM tag
                , nest 2 $ prettyTCM sc
                ]
              throwError (GenericSplitError "precomputed set of constructors does not cover all cases")

      liftTCM $ inContextOfT $ checkSortOfSplitVar dr (unDom t) delta2 target
      return $ Right $ Covering (lookupPatternVar sc x) ns

  where
    inContextOfT, inContextOfDelta2 :: (MonadTCM tcm, MonadAddContext tcm, MonadDebug tcm) => tcm a -> tcm a
    inContextOfT      = addContext tel . escapeContext impossible (x + 1)
    inContextOfDelta2 = addContext tel . escapeContext impossible x

    -- Debug printing
    debugInit tel x ps cps = liftTCM $ inTopContext $ do
      reportSDoc "tc.cover.top" 10 $ vcat
        [ "TypeChecking.Coverage.split': split"
        , nest 2 $ vcat
          [ "tel     =" <+> prettyTCM tel
          , "x       =" <+> prettyTCM x
          , "ps      =" <+> do addContext tel $ prettyTCMPatternList $ fromSplitPatterns ps
          , "cps     =" <+> prettyTCM cps
          ]
        ]
      reportSDoc "tc.cover.top" 60 $ vcat
        [ "TypeChecking.Coverage.split': split"
        , nest 2 $ vcat
          [ "tel     =" <+> (text . show) tel
          , "x       =" <+> (text . show) x
          , "ps      =" <+> (text . show) ps
          , "cps     =" <+> (text . show) cps
          ]
        ]

    debugHoleAndType delta1 delta2 s ps t =
      liftTCM $ reportSDoc "tc.cover.top" 10 $ nest 2 $ vcat $
        [ "p      =" <+> text (patVarNameToString s)
        , "ps     =" <+> prettyTCMPatternList ps
        , "delta1 =" <+> prettyTCM delta1
        , "delta2 =" <+> inContextOfDelta2 (prettyTCM delta2)
        , "t      =" <+> inContextOfT (prettyTCM t)
        ]


-- | splitResult for MakeCase, tries to introduce IApply or ProjP copatterns
splitResult :: QName -> SplitClause -> TCM (Either SplitError [SplitClause])
splitResult f sc = do
  caseMaybeM (splitResultPath f sc)
             ((fmap . fmap) splitClauses $ splitResultRecord f sc)
             (return . Right . (:[]))


-- | Tries to split the result to introduce an IApply pattern.
splitResultPath :: QName -> SplitClause -> TCM (Maybe SplitClause)
splitResultPath f sc@(SClause tel ps _ _ target) = do
  caseMaybe target (return Nothing) $ \ t -> do
        caseMaybeM (isPath (unDom t)) (return Nothing) $ \ _ -> do
               (TelV i b, boundary) <- telViewUpToPathBoundary' 1 (unDom t)
               let tel' = abstract tel i
                   rho  = raiseS 1
                   ps' = applySubst rho (scPats sc) ++ telePatterns i boundary
                   cps' = applySubst rho (scCheckpoints sc)
                   target' = Just $ b <$ t
               return . Just $ SClause tel' ps' idS cps' target'

-- | @splitResultRecord f sc = return res@
--
--   If the target type of @sc@ is a record type, a covering set of
--   split clauses is returned (@sc@ extended by all valid projection patterns),
--   otherwise @res == Left _@.
--   Note that the empty set of split clauses is returned if the record has no fields.
splitResultRecord :: QName -> SplitClause -> TCM (Either SplitError Covering)
splitResultRecord f sc@(SClause tel ps _ _ target) = do
  reportSDoc "tc.cover.split" 10 $ vcat
    [ "splitting result:"
    , nest 2 $ "f      =" <+> prettyTCM f
    , nest 2 $ "target =" <+> addContext tel (maybe empty prettyTCM target)
    ]
  -- if we want to split projections, but have no target type, we give up
  let failure = return . Left
  caseMaybe target (failure CosplitNoTarget) $ \ t -> do
    isR <- addContext tel $ isRecordType $ unDom t
    case isR of
      Just (_r, vs, Record{ recFields = fs }) -> do
        reportSDoc "tc.cover" 20 $ sep
          [ text $ "we are of record type _r = " ++ prettyShow _r
          , text   "applied to parameters vs =" <+> addContext tel (prettyTCM vs)
          , text $ "and have fields       fs = " ++ prettyShow fs
          ]
        -- Andreas, 2018-06-09, issue #2170, we always have irrelevant projections
        -- available on the lhs.
        -- -- Andreas, 2018-03-19, issue #2971, check that we have a "strong" record type,
        -- -- i.e., with all the projections.  Otherwise, we may not split.
        -- ifNotM (strongRecord fs) (failure CosplitIrrelevantProjections) $ {-else-} do
        let es = patternsToElims $ fromSplitPatterns ps
        -- Note: module parameters are part of ps
        let self  = defaultArg $ Def f [] `applyE` es
            pargs = vs ++ [self]
            fieldValues = for fs $ \ proj -> unArg self `applyE` [Proj ProjSystem (unDom proj)]
        reportSDoc "tc.cover" 20 $ addContext tel $ sep
          [ text   "we are              self =" <+> prettyTCM (unArg self)
          , text   "            field values =" <+> prettyTCM fieldValues
          ]
        let n = defaultArg $ permRange $ fromMaybe __IMPOSSIBLE__ $ dbPatPerm $ fromSplitPatterns ps
            -- Andreas & James, 2013-11-19 includes the dot patterns!
            -- See test/succeed/CopatternsAndDotPatterns.agda for a case with dot patterns
            -- and copatterns which fails for @n = size tel@ with a broken case tree.

        -- Andreas, 2016-07-22 read the style of projections from the user's lips
        projOrigin <- ifM (optPostfixProjections <$> pragmaOptions) (return ProjPostfix) (return ProjPrefix)
        Right . Covering n <$> do
          forM (zip fs $ List.inits fieldValues) $ \ (proj, prevFields) -> do
            -- compute the new target
            dType <- defType <$> do getConstInfo $ unDom proj -- WRONG: typeOfConst $ unArg proj
            let -- Substitution for parameters and previous fields. Needs to be applied to potential
                -- tactic in proj.
                fieldSub = reverse (map unArg vs ++ prevFields) ++# EmptyS impossible
                proj'    = applySubst fieldSub proj
                -- type of projection instantiated at self
                target' = Just $ proj' $> dType `piApply` pargs      -- Always visible (#2287)
                projArg = fmap (Named Nothing . ProjP projOrigin) $ argFromDom $ setHiding NotHidden proj
                sc' = sc { scPats   = scPats sc ++ [projArg]
                         , scSubst  = idS
                         , scTarget = target'
                         }
            reportSDoc "tc.cover.copattern" 40 $ vcat
              [ "fieldSub for" <+> prettyTCM (unDom proj)
              , nest 2 $ pretty fieldSub ]
            return (SplitCon (unDom proj), (sc', NoInfo))
      _ -> addContext tel $ do
        buildClosure (unDom t) >>= failure . CosplitNoRecordType
  -- Andreas, 2018-06-09, issue #2170: splitting with irrelevant fields is always fine!
  -- where
  -- -- A record type is strong if it has all the projections.
  -- -- This is the case if --irrelevant-projections or no field is irrelevant.
  -- -- TODO: what about shape irrelevance?
  -- strongRecord :: [Arg QName] -> TCM Bool
  -- strongRecord fs = (optIrrelevantProjections <$> pragmaOptions) `or2M`
  --   (return $ not $ any isIrrelevant fs)


-- * Boring instances

-- | For debugging only.
instance PrettyTCM SplitClause where
  prettyTCM (SClause tel pats sigma cps target) = sep
    [ "SplitClause"
    , nest 2 $ vcat
      [ "tel          =" <+> prettyTCM tel
      , "pats         =" <+> sep (map (prettyTCM . namedArg) pats)
      , "subst        =" <+> prettyTCM sigma
      , "checkpoints  =" <+> prettyTCM cps
      , "target       =" <+> do
          caseMaybe target empty $ \ t -> do
            addContext tel $ prettyTCM t
      -- Triggers crash (see Issue 1374).
      -- , "subst target = " <+> do
      --     caseMaybe target empty $ \ t -> do
      --       addContext tel $ prettyTCM $ applySubst sigma t
      ]
    ]

{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE NoMonomorphismRestriction #-} -- TODO remove

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
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Translation.InternalToAbstract (NamedClause(..))

import Agda.TypeChecking.Names
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.Monad

import Agda.TypeChecking.Rules.LHS (checkSortOfSplitVar)
import Agda.TypeChecking.Rules.LHS.Problem (allFlexVars)
import Agda.TypeChecking.Rules.LHS.Unify
import Agda.TypeChecking.Rules.Term (unquoteTactic)

import Agda.TypeChecking.Coverage.Match
import Agda.TypeChecking.Coverage.SplitTree

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
import Agda.Utils.Except
  ( ExceptT
  , MonadError (throwError, catchError)
  , runExceptT
  )
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.WithDefault

import Agda.Utils.Impossible

data SplitClause = SClause
  { scTel    :: Telescope
    -- ^ Type of variables in @scPats@.
  , scPats   :: [NamedArg SplitPattern]
    -- ^ The patterns leading to the currently considered branch of
    --   the split tree.
  , scSubst  :: Substitution' SplitPattern
    -- ^ Substitution from 'scTel' to old context.
    --   Only needed directly after split on variable:
    --   * To update 'scTarget'
    --   * To rename other split variables when splitting on
    --     multiple variables.
    --   @scSubst@ is not ``transitive'', i.e., does not record
    --   the substitution from the original context to 'scTel'
    --   over a series of splits.  It is freshly computed
    --   after each split by 'computeNeighborhood'; also
    --   'splitResult', which does not split on a variable,
    --   should reset it to the identity 'idS', lest it be
    --   applied to 'scTarget' again, leading to Issue 1294.
  , scCheckpoints :: Map CheckpointId Substitution
    -- ^ We need to keep track of the module parameter checkpoints for the
    -- clause for the purpose of inferring missing instance clauses.
  , scTarget :: Maybe (Dom Type)
    -- ^ The type of the rhs, living in context 'scTel'.
    --   'fixTargetType' computes the new 'scTarget' by applying
    --   substitution 'scSubst'.
  }

-- | A @Covering@ is the result of splitting a 'SplitClause'.
data Covering = Covering
  { covSplitArg     :: Arg Nat
     -- ^ De Bruijn level (counting dot patterns) of argument we split on.
  , covSplitClauses :: [(SplitTag, (SplitClause, IInfo))]
      -- ^ Covering clauses, indexed by constructor/literal these clauses share.
  }

-- | Project the split clauses out of a covering.
splitClauses :: Covering -> [SplitClause]
splitClauses (Covering _ qcs) = map (fst . snd) qcs

-- | Create a split clause from a clause in internal syntax. Used by make-case.
clauseToSplitClause :: Clause -> SplitClause
clauseToSplitClause cl = SClause
  { scTel    = clauseTel cl
  , scPats   = toSplitPatterns $ namedClausePats cl
  , scSubst  = idS  -- Andreas, 2014-07-15  TODO: Is this ok?
  , scCheckpoints = Map.empty -- #2996: not __IMPOSSIBLE__ for debug printing
  , scTarget = domFromArg <$> clauseType cl
  }

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
  reportSLn "tc.cover.top" 30 $ "entering coverageCheck for " ++ show f
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
  whenM (optCubical <$> pragmaOptions) $ do
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
      let cl = Clause { clauseLHSRange    = noRange
                      , clauseFullRange   = noRange
                      , clauseTel         = tel
                      , namedClausePats   = applySubst sub ps
                      , clauseBody        = Nothing
                      , clauseType        = Nothing
                      , clauseCatchall    = False
                      , clauseRecursive   = Just False
                      , clauseUnreachable = Just False
                      , clauseEllipsis    = NoEllipsis
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
  let (is0, cs1) = unzip $ for (zip [0..] cs) $ \ (i, cl) ->
        let unreachable = i `IntSet.notMember` used in
        (boolToMaybe unreachable i, cl { clauseUnreachable = Just unreachable  })
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
  (_ , sc') <- insertTrailingArgs sc
  CoverResult { coverMissingClauses = missing } <- cover f cs sc'
  return $ null missing
 -- Andreas, 2019-08-08 and 2020-02-11
 -- If there is an error (e.g. unification error), don't report it
 -- to the user.  Rather, assume the clause is not already covered.
 `catchError` \ _ -> return False

data CoverResult = CoverResult
  { coverSplitTree       :: SplitTree
  , coverUsedClauses     :: IntSet -- Set Nat
  , coverMissingClauses  :: [(Telescope, [NamedArg DeBruijnPattern])]
  , coverPatterns        :: [Clause]
  -- ^ The set of patterns used as cover.
  , coverNoExactClauses  :: IntSet -- Set Nat
  }

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
  match cs ps >>= \case
    Yes (i,mps) -> do
      exact <- allM (map snd mps) isTrivialPattern
      let cl0 = indexWithDefault __IMPOSSIBLE__ cs i
      let noExactClause = if exact || clauseCatchall (indexWithDefault __IMPOSSIBLE__ cs i)
                          then empty
                          else singleton i
      reportSLn "tc.cover.cover" 10 $ "pattern covered by clause " ++ show i
      reportSDoc "tc.cover.cover" 20 $ text "with mps = " <+> do addContext tel $ pretty $ mps
      cl <- applyCl sc cl0 mps
      return $ CoverResult (SplittingDone (size tel)) (singleton i) [] [cl] noExactClause

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
    -- | When we get a SplitError, tighten the error Range to the clauses
    -- that are still candidates for covering the SplitClause.
    splitError :: SplitError -> TCM a
    splitError = withRangeOfCandidateClauses . typeError . SplitError

    -- | This repeats the matching, but since we are crashing anyway,
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

    applyCl :: SplitClause -> Clause -> [(Nat, SplitPattern)] -> TCM Clause
    applyCl SClause{scTel = tel, scPats = sps} cl mps = addContext tel $ do
        let ps = namedClausePats cl
        reportSDoc "tc.cover.applyCl" 40 $ "applyCl"
        reportSDoc "tc.cover.applyCl" 40 $ "tel    =" <+> prettyTCM tel
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
                    , clauseCatchall  = clauseCatchall cl
                    , clauseRecursive = clauseRecursive cl
                    , clauseUnreachable = clauseUnreachable cl
                    , clauseEllipsis  = clauseEllipsis cl
                    }
      where
        (vs,qs) = unzip mps
        mps' = zip vs $ map namedArg $ fromSplitPatterns $ map defaultNamedArg qs
        s = parallelS (for [0..maximum (-1:vs)] $ (\ i -> fromMaybe (deBruijnVar i) (List.lookup i mps')))

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
          cs <- do
            let fallback = return cs
            caseMaybeM (getPrimitiveName' builtinHComp) fallback $ \ comp -> do
            let isComp = \case
                  SplitCon c -> comp == c
                  _ -> False
            caseMaybe (List.find (isComp . fst) scs) fallback $ \ (_, newSc) -> do
            snoc cs <$> createMissingHCompClause f n x sc newSc
          (mtrees,cs) <- fmap (cs ++) <$> createMissingIndexedClauses f n x sc scs'
          results <- mapM ((cover f cs) . snd) scs
          let trees = map coverSplitTree      results
              useds = map coverUsedClauses    results
              psss  = map coverMissingClauses results
              qsss  = map coverPatterns results
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
              tree   = SplitAt n StrictSplit (trees' ++ mtrees) -- TODO: Lazy?
          return $ CoverResult tree (IntSet.unions useds) (concat psss) (concat qsss) (IntSet.unions noex)

    -- Try to split result
    trySplitRes
      :: BlockedOnResult -- ^ Are we blocked on the result?
      -> Bool            -- ^ Is this the last thing we try?
      -> (SplitError -> TCM CoverResult) -- ^ Handler for 'SplitError'
      -> TCM CoverResult -- ^ Continuation
      -> TCM CoverResult
    -- not blocked on result: try regular splits
    trySplitRes NotBlockedOnResult finalSplit splitError cont
      | finalSplit = __IMPOSSIBLE__ -- there must be *some* reason we are blocked
      | otherwise  = cont
    -- blocked on arguments that are not yet introduced:

    -- we must split on a variable so that the target type becomes a pi type
    trySplitRes (BlockedOnApply IsApply) finalSplit splitError cont
      | finalSplit = __IMPOSSIBLE__ -- already ruled out by lhs checker
      | otherwise  = cont
    -- ...or it was an IApply pattern, so we might just need to introduce the variable now.
    trySplitRes (BlockedOnApply IsIApply) finalSplit splitError cont
       = do
         caseMaybeM (splitResultPath f sc) fallback $ (cover f cs . snd) <=< insertTrailingArgs
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
            mapM (traverseF $ cover f cs <=< (snd <.> insertTrailingArgs)) (map (\(t,(sc,i)) -> (t,sc)) scs)
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


createMissingIndexedClauses :: QName
                            -> Arg Nat
                            -> BlockingVar
                            -> SplitClause
                            -> [(SplitTag,(SplitClause,IInfo))]
                            -> TCM ([(SplitTag,SplitTree)],[Clause])
createMissingIndexedClauses f n x old_sc scs = do
  reflId <- getName' builtinReflId
  let infos = [(c,i) | (SplitCon c, (_,TheInfo i)) <- scs ]
  case scs of
    [(SplitCon c,(_newSc,i@TheInfo{}))] | Just c == reflId -> unzip . maybeToList <$> createMissingConIdClause f n x old_sc i
    xs | not $ null infos -> do
         reportSDoc "tc.cover.indexed" 20 $ text "size (xs,infos):" <+> pretty (size xs,size infos)
         reportSDoc "tc.cover.indexed" 20 $ text "xs :" <+> pretty (map fst xs)

         unless (size xs == size infos + 1) $ __IMPOSSIBLE__
         Constructor{conData} <- theDef <$> getConstInfo (fst (head infos))
         Datatype{dataPars = pars, dataIxs = nixs, dataTranspIx} <- theDef <$> getConstInfo conData
         hcomp <- fromMaybe __IMPOSSIBLE__ <$> getName' builtinHComp
         trX <- fromMaybe __IMPOSSIBLE__ <$> pure dataTranspIx
         trX_cl <- createMissingTrXTrXClause trX f n x old_sc
         hcomp_cl <- createMissingTrXHCompClause trX f n x old_sc
         (trees,cls) <- fmap unzip . forM infos $ \ (c,i) -> do
           cl <- createMissingTrXConClause trX f n x old_sc c i
           return $ ((SplitCon c , SplittingDone (size $ clauseTel cl)) , cl)
         let extra = [ (SplitCon trX, SplittingDone $ size $ clauseTel trX_cl)
                                           , (SplitCon hcomp, SplittingDone $ size $ clauseTel hcomp_cl)
                                           ]
                 --  = [ (SplitCon trX, SplittingDone $ size $ clauseTel trX_cl) ]
             extraCl = [trX_cl, hcomp_cl]
                 --  = [trX_cl]
         let tree = (SplitCon trX,) $ SplitAt ((+(pars+nixs+1)) <$> n) StrictSplit $
                                           trees
                                        ++ extra
         reportSDoc "tc.cover.indexed" 20 $
           "tree:" <+> pretty tree
         let clauses = extraCl ++ cls
         addClauses f clauses
         return $ ([tree],clauses)
--         return $ ([],[])
    xs | otherwise -> return ([],[])

createMissingTrXTrXClause :: QName -- ^ trX
                            -> QName -- ^ f defined
                            -> Arg Nat
                            -> BlockingVar
                            -> SplitClause
                            -> TCM Clause
createMissingTrXTrXClause q_trX f n x old_sc = do
  let
   old_tel = scTel old_sc
   old_ps = fromSplitPatterns $ scPats old_sc
   old_t = fromMaybe __IMPOSSIBLE__ $ scTarget old_sc

  reportSDoc "tc.cover.trx.trx" 20 $ "trX-trX clause for" <+> prettyTCM f
  reportSDoc "tc.cover.trx.trx" 20 $ nest 2 $ vcat $
    [ "old_tel:" <+> prettyTCM old_tel
    , "old_ps :" <+> addContext old_tel (prettyTCM $ patternsToElims old_ps)
    , "old_t  :" <+> addContext old_tel (prettyTCM old_t)
    ]

  -- TODO: redo comments, the strategy changed.
  -- old_tel = Γ1, (x : D η v), Δ
  -- α = boundary(old_ps)
  -- Γ1, (x : D η v), Δ ⊢ f old_ps : old_t [ α ↦ (f old_ps)[α] ]

  -- α' = boundary(old_ps[x = pat])
  -- Γ1, φ : I, p : Path X(η) _ v, ψ : I, q : Path X(η) _ (p i0), x0 : D η (q i0) ⊢ pat := trX p φ (trX q ψ x0) : D η v

  -- Ξ = Γ1, φ : I, p : Path X(η) _ v, ψ : I, q : Path X(η) _ (p i0), x0 : D η (q i0), Δ[x = pat]

  -- Ξ ⊢ w1 := f old_ps[γ1,x = pat,δ] : old_t[γ1,x = pat,δ] -- the case we are defining. can only be used if specialized.

  -- Ξ ⊢ rhs : old_t[γ1,x = pat,δ] [ α' ↦ w1[α']
                                -- , φ  ↦ w1[φ = i1, p = refl]
                                -- , ψ  ↦ w1[ψ = i1, q = refl]
                                -- ]
  -- Ξ ⊢ q2 := tr (i. Path X(η) (q i0) (p i)) φ q : Path X(η) (q i0) (p i1)
  -- Ξ ⊢ pat_rec[0] = pat : D η v
  -- Ξ ⊢ pat_rec[1] = trX q2 (φ ∧ ψ) x0 : D η v
  -- Ξ ⊢ pat-rec[i] := trX (\ j → p (i ∨ j)) (i ∨ φ) (trX (q2_f i) (ψ ∧ (φ ∨ ~ i)) t)

  -- Ξ ⊢ δ_f[1] = tr (i. Δ[γ1,x = pat_rec[i]]) (φ ∧ ψ) δ
  -- Ξ ⊢ w0 := f old_ps[γ1,x = pat_rec[1] ,δ_f[1]] : old_t[γ1,x = pat_rec[1],δ_f[1]]
  -- Ξ ⊢ rhs := tr (i. old_t[γ1,x = pat_rec[~i], δ_f[~i]]) (φ ∧ ψ) w0 -- TODO plus sides.

  interval <- elInf primInterval
  iz <- primIZero
  io <- primIOne
  tHComp <- primHComp
  tNeg <- primINeg
  let neg i = pure tNeg <@> i
  let min i j = cl primIMin <@> i <@> j
  let max i j = cl primIMax <@> i <@> j
  let
    old_tel = scTel old_sc
    old_ps' = AbsN (teleNames old_tel) $ fromSplitPatterns $ scPats old_sc
    old_ps = pure $ old_ps'
    old_ty = pure $ AbsN (teleNames old_tel) $ fromMaybe __IMPOSSIBLE__ $ scTarget old_sc
  -- old_tel = Γ(x: D η v)Δ
  -- Γ1, (x : D η v)  ⊢ delta = (δ : Δ)
    (gamma1x,delta') = splitTelescopeAt (size old_tel - blockingVarNo x) old_tel
    delta = pure $ AbsN (teleNames gamma1x) $ delta'
    gamma1_size = (size gamma1x - 1)
    (gamma1,ExtendTel dType' _) = splitTelescopeAt gamma1_size gamma1x

  old_sides <- forM old_ps' $ \ ps -> do
    let vs = iApplyVars ps
    let tm = Def f $ patternsToElims ps
    xs <- forM vs $ \ v ->
        -- have to reduce these under the appropriate substitutions, otherwise non-normalizing(?)
          fmap (var v,) . reduce $ (inplaceS v iz `applySubst` tm, inplaceS v io `applySubst` tm)
    return $ concatMap (\(v,(l,r)) -> [(tNeg `apply` [argN v],l),(v,r)]) xs
  let
    gamma1ArgNames = teleArgNames gamma1
    deltaArgNames = teleArgNames delta'
  (params,xTel,dT) <- addContext gamma1 $ do
    Right (IsData, d, ps, _is, _cs, _) <- runExceptT $ isDatatype Inductive dType'
    def <- getConstInfo d
    let dTy = defType def
    let Datatype{dataSort = s} = theDef def
    TelV tel _ <- telView dTy
    let params = AbsN (teleNames gamma1) ps
        xTel = AbsN (teleNames gamma1) (tel `apply` ps)

    dT <- runNamesT [] $ do
          s <- open $ AbsN (teleNames tel) s
          bindNArg (teleArgNames gamma1) $ \ g1 -> do
          bindNArg (teleArgNames $ unAbsN xTel) $ \ x -> do
          params <- pure params `applyN` (fmap unArg <$> g1)
          x      <- sequence x
          s <- s `applyN` (map (pure . unArg) $ params ++ x)
          pure $ El s $ Def d [] `apply` (params ++ x)
    return $ (params, xTel,dT)

  let
    xTelI = pure $ expTelescope interval <$> xTel
    xTelIArgNames = teleArgNames (unAbsN xTel) -- same names

  -- Γ1, φ, p, ψ, q, x0 ⊢ pat := trX p φ (trX q ψ x0)
  let trX' = bindNArg gamma1ArgNames $ \ g1 -> do
             bindNArg ([defaultArg "phi"] ++ xTelIArgNames) $ \ phi_p -> do
             bindNArg [defaultArg "x0"] $ \ x0 -> do
             param_args <- fmap (map (setHiding Hidden . fmap (unnamed . dotP))) $
               pure params `applyN` (fmap unArg <$> g1)
             (phi:p) <- sequence phi_p
             x0 <- sequence x0
             pure $ DefP defaultPatternInfo q_trX $ param_args ++ p ++ [phi] ++ x0
      trX = (fmap . fmap . fmap) patternToTerm <$> trX'
  let pat' =
            bindN (map unArg gamma1ArgNames) $ \ g1 -> do
            bindN (map unArg $ ([defaultArg "phi"] ++ xTelIArgNames)) $ \ phi_p -> do
            bindN (map unArg $ ([defaultArg "psi"] ++ xTelIArgNames)) $ \ psi_q -> do
            bindN (map unArg $ [defaultArg "x0"]) $ \ x0 -> do
            -- (phi:p) <- sequence phi_p
            -- (psi:q) <- sequence psi_q
            -- x0 <- sequence x0
            let trX = trX' `applyN` g1
            trX `applyN` phi_p `applyN` [trX `applyN` psi_q `applyN` x0]
          --  pure $ trX $ p ++ [phi, defaultArg $ unnamed $ trX $ q ++ [psi] ++ x0]
      pat = (fmap . fmap . fmap . fmap) patternToTerm <$> pat'
  let deltaPat g1 phi p psi q x0 =
        delta `applyN` (g1 ++ [pat `applyN` g1 `applyN` (phi:p) `applyN` (psi:q) `applyN` [x0]])
  -- Ξ
  cTel <- runNamesT [] $
    abstractN (pure gamma1) $ \ g1 -> do
    abstractT "φ" (pure interval) $ \ phi -> do
    abstractN (xTelI `applyN` g1) $ \ p -> do
    abstractT "ψ" (pure interval) $ \ psi -> do
    abstractN (xTelI `applyN` g1) $ \ q -> do
    abstractT "x0" (pure dT `applyN` g1 `applyN` (flip map q $ \ f -> f <@> pure iz)) $ \ x0 -> do
    deltaPat g1 phi p psi q x0

  ps_ty_rhs <- runNamesT [] $ do
    bindN (map unArg gamma1ArgNames) $ \ g1 -> do
    bind "φ" $ \ phi -> do
    bindN (map unArg xTelIArgNames) $ \ p -> do
    bind "ψ" $ \ psi -> do
    bindN (map unArg xTelIArgNames) $ \ q -> do
    bind "x0" $ \ x0 -> do
    bindN (map unArg deltaArgNames) $ \ d -> do
    let
      ps :: NamesT TCM NAPs
      ps = old_ps `applyN` (g1
                          ++ [pat' `applyN` g1 `applyN` (phi:p) `applyN` (psi:q) `applyN` [x0]]
                          ++ d)

      rhsTy = old_ty `applyN` (g1
                          ++ [pat `applyN` g1 `applyN` (phi:p) `applyN` (psi:q) `applyN` [x0]]
                          ++ d)

    xTel <- (open =<<) $ pure xTel `applyN` g1
    q4_f <- (open =<<) $ bind "i" $ \ i -> lamTel $ bind "j" $ \ j -> do
      ty <- bind "i" $ \ _ -> xTel
      face <- max phi $ max (neg j) (neg i)
      base <- map defaultArg <$> appTel (sequence q) j
      u  <- liftM2 (,) (max j psi) $ bind "h" $ \ h -> do
              appTel (sequence p) (min j (min h i))
      Right xs <- lift $ runExceptT $ transpSysTel' False ty [u] face base
      pure $ map unArg xs
    -- Ξ ⊢ pat_rec[0] = pat : D η v
    -- Ξ ⊢ pat_rec[1] = trX q4 (φ ∧ ψ) x0 : D η v
    -- Ξ ⊢ pat-rec[i] := trX (\ j → p (i ∨ j)) (i ∨ φ) (trX (q4_f i) (ψ ∧ (φ ∨ ~ i)) t)
    pat_rec <- (open =<<) $ bind "i" $ \ i -> do
          p_conn <- (mapM open =<<) $ lamTel $ bind "i" $ \ j -> sequence p `appTel` max i j
          q4_f' <- (mapM open =<<) $ absApp <$> q4_f <*> i
          trX `applyN` g1 `applyN` (max i phi:p_conn)
              `applyN` [trX `applyN` g1 `applyN` (min psi (max phi (neg i)):q4_f') `applyN` [x0]]

    let mkBndry args = do
            args1 <- (mapM open =<<) $ (absApp <$> args <*> pure io)
            -- faces ought to be constant on "j"
            faces <- pure (fmap (map fst) old_sides) `applyN` args1
            us <- forM (sequence (fmap (map snd) old_sides)) $ \ u -> do
                  lam "j" $ \ j -> ilam "o" $ \ _ -> do
                    args <- (mapM open =<<) $ (absApp <$> args <*> j)
                    pure u `applyN` args
            forM (zip faces us) $ \ (phi,u) -> liftM2 (,) (open phi) (open u)
    let mkComp pr = bind "i" $ \ i -> do
          d_f <- (open =<<) $ bind "j" $ \ j -> do
            tel <- bind "j" $ \ j -> delta `applyN` (g1 ++ [pr `applyN` [i,j]])
            face <- min phi psi `max` (min i (max phi psi))
            j <- j
            d <- map defaultArg <$> sequence d
            Right d_f <- lift $ runExceptT $ trFillTel tel face d j
            pure $ map unArg d_f
          let args = bind "j" $ \ j -> do
                g1 <- sequence g1
                x <- pr `applyN` [i,neg j]
                ys <- absApp <$> d_f <*> neg j
                pure $ g1 ++ x:ys
          ty <- (open =<<) $ bind "j" $ \ j -> do
               args <- (mapM open =<<) $ absApp <$> args <*> j
               fmap unDom $ old_ty `applyN` args
          let face = max i (min phi psi)
          base <- (open =<<) $ do
            args' <- (mapM open =<<) $ absApp <$> args <*> pure iz
            fmap (Def f) $ (fmap patternsToElims <$> old_ps) `applyN` args'
          sys <- mkBndry args
          transpSys ty sys face base

    -- Ξ ⊢ δ_f[1] = tr (i. Δ[γ1,x = pat_rec[i]]) (φ ∧ ψ) δ
    -- Ξ ⊢ w0 := f old_ps[γ1,x = pat_rec[1] ,δ_f[1]] : old_t[γ1,x = pat_rec[1],δ_f[1]]
    -- Ξ ⊢ rhs := tr (i. old_t[γ1,x = pat_rec[~i], δ_f[~i]]) (φ ∧ ψ) w0 -- TODO plus sides.
    syspsi <- (open =<<) $ lam "i" $ \ i -> ilam "o" $ \ _ -> do
      c <- mkComp $ bindN ["i","j"] $ \ ij -> do
        let i = ij List.!! 0
            j = ij List.!! 1
        Abs n (data_ty,lines) <- bind "k" $ \ k -> do
          let phi_k = max phi (neg k)
          let p_k = flip map p $ \ p -> lam "h" $ \ h -> p <@> (min k h)
          data_ty <- pure dT `applyN` g1 `applyN` (flip map p $ \ p -> p <@> k)
          line1 <- trX `applyN` g1 `applyN` (phi_k:p_k) `applyN` [x0]

          line2 <- trX `applyN` g1
                       `applyN` (max phi_k j      : (flip map p_k $ \ p -> lam "h" $ \ h -> p <@> (max h j)))
                       `applyN`
                  [trX `applyN` g1
                       `applyN` (max phi_k (neg j): (flip map p_k $ \ p -> lam "h" $ \ h -> p <@> (min h j)))
                       `applyN` [x0]]
          pure (data_ty,[line1,line2])
        data_ty <- open $ Abs n data_ty
        [line1,line2] <- mapM (open . Abs n) lines
        let sys = [(neg i, lam "k" $ \ k -> ilam "o" $ \ _ -> absApp <$> line2 <*> k)
                  ,(neg j `max` j `max` i `max` phi, lam "k" $ \ k -> ilam "o" $ \ _ -> absApp <$> line1 <*> k)
                  ]
        transpSys data_ty sys (pure iz) x0
      absApp <$> pure c <*> i
    sysphi <- (open =<<) $ lam "i" $ \ i -> ilam "o" $ \ o -> do
      c <- mkComp $ bindN ["i","j"] $ \ ij -> do
        let i = ij List.!! 0
            j = ij List.!! 1
        trX `applyN` g1 `applyN` (psi:q) `applyN` [x0]
      absApp <$> pure c <*> i
    syse <- mkBndry $ bind "j" $ \ _ -> sequence $ g1 ++ [absApp <$> pat_rec <*> pure iz] ++ d
    let sys = syse ++ [(phi,sysphi)] ++ [(psi,syspsi)]
    w0 <- (open =<<) $ do
      let w = mkComp (bindN ["i","j"] $ \ ij -> absApp <$> pat_rec <*> (ij List.!! 1))
      absApp <$> w <*> pure iz
    let rhs = hcomp (unDom <$> rhsTy) sys w0
    (,,) <$> ps <*> rhsTy <*> rhs
  let (ps,ty,rhs) = unAbsN $ unAbs $ unAbsN $ unAbs $ unAbsN $ unAbs $ unAbsN $ ps_ty_rhs
  reportSDoc "tc.cover.trx.trx" 20 $ "trX-trX clause for" <+> prettyTCM f
  let c = Clause { clauseTel = cTel
                  , namedClausePats = ps
                  , clauseBody = Just rhs
                  , clauseType = Just $ Arg (getArgInfo ty) (unDom ty)
                  , clauseLHSRange = noRange
                  , clauseFullRange = noRange
                  , clauseCatchall = False
                  , clauseRecursive = Just True
                  , clauseUnreachable = Just False
                  , clauseEllipsis = NoEllipsis
                  }
  debugClause "tc.cover.trx.trx" c
  return $ c
createMissingTrXHCompClause :: QName
                            -> QName
                            -> Arg Nat
                            -> BlockingVar
                            -> SplitClause
                            -> TCM Clause
createMissingTrXHCompClause q_trX f n x old_sc = do
  let
   old_tel = scTel old_sc
   old_ps = fromSplitPatterns $ scPats old_sc
   old_t = fromMaybe __IMPOSSIBLE__ $ scTarget old_sc

  reportSDoc "tc.cover.trx.hcomp" 20 $ "trX-hcomp clause for" <+> prettyTCM f
  reportSDoc "tc.cover.trx.hcomp" 20 $ nest 2 $ vcat $
    [ "old_tel:" <+> prettyTCM old_tel
    , "old_ps :" <+> addContext old_tel (prettyTCM $ patternsToElims old_ps)
    , "old_t  :" <+> addContext old_tel (prettyTCM old_t)
    ]

  -- old_tel = Γ1, (x : D η v), Δ
  -- α = boundary(old_ps)
  -- Γ1, (x : D η v), Δ ⊢ f old_ps : old_t [ α ↦ (f old_ps)[α] ]

  -- α' = boundary(old_ps[x = pat])
  -- Γ1, φ : I, p : Path X(η) _ v, ψ : I, u : I -> [ψ] → D η (p i0), u0 : D η (p i0) ⊢ pat := trX p φ (hcomp ψ u u0) : D η v

  -- Ξ = Γ1, φ : I, p : Path X(η) _ v, ψ : I, u : ..., u0 : D η (p i0), Δ[x = pat]

  -- Ξ ⊢ w1 := f old_ps[γ1,x = pat,δ] : old_t[γ1,x = pat,δ] -- the case we are defining. can only be used if specialized.

  -- Ξ ⊢ rhs : old_t[γ1,x = pat,δ] [ α' ↦ w1[α']
                                -- , φ  ↦ w1[φ = i1, p = refl]   = f old_ps[γ1,x = hcomp ψ u u0    ,δ]
                                -- , ψ  ↦ w1[ψ = i1]             = f old_ps[γ1,x = trX p φ (u i1 _),δ]
                                -- ]

  -- Ξ ⊢ q2 := tr (i. Path X(η) (q i0) (p i)) φ q : Path X(η) (q i0) (p i1)
  -- Ξ ⊢ pat_rec[0] = pat : D η v
  -- Ξ ⊢ pat_rec[1] = trX q2 (φ ∧ ψ) x0 : D η v
  -- Ξ ⊢ pat-rec[i] := trX (\ j → q (i ∨ j)) (i ∨ φ) (trX (q2_f i) (ψ ∧ (φ ∨ ~ i)) t)

  -- Ξ ⊢ δ_f[1] = tr (i. Δ[γ1,x = pat_rec[i]]) (φ ∧ ψ) δ : Δ[γ1,x = pat_rec[1]]
  -- Ξ ⊢ w0 := f old_ps[γ1,x = pat_rec[1] ,δ_f[1]] : old_t[γ1,x = pat_rec[1],δ_f[1]]
  -- Ξ ⊢ rhs := tr (i. old_t[γ1,x = pat_rec[~i], δ_f[~i]]) (φ ∧ ψ) w0 -- TODO plus sides.

  q_hcomp <- fromMaybe __IMPOSSIBLE__ <$> getName' builtinHComp
  let
   old_tel = scTel old_sc
   old_ps = fromSplitPatterns $ scPats old_sc
   old_t = fromMaybe __IMPOSSIBLE__ $ scTarget old_sc

  reportSDoc "tc.cover.trx.trx" 20 $ "trX-trX clause for" <+> prettyTCM f
  reportSDoc "tc.cover.trx.trx" 20 $ nest 2 $ vcat $
    [ "old_tel:" <+> prettyTCM old_tel
    , "old_ps :" <+> addContext old_tel (prettyTCM $ patternsToElims old_ps)
    , "old_t  :" <+> addContext old_tel (prettyTCM old_t)
    ]

  -- TODO: redo comments, the strategy changed.
  -- old_tel = Γ1, (x : D η v), Δ
  -- α = boundary(old_ps)
  -- Γ1, (x : D η v), Δ ⊢ f old_ps : old_t [ α ↦ (f old_ps)[α] ]

  -- α' = boundary(old_ps[x = pat])
  -- Γ1, φ : I, p : Path X(η) _ v, ψ : I, q : Path X(η) _ (p i0), x0 : D η (q i0) ⊢ pat := trX p φ (trX q ψ x0) : D η v

  -- Ξ = Γ1, φ : I, p : Path X(η) _ v, ψ : I, q : Path X(η) _ (p i0), x0 : D η (q i0), Δ[x = pat]

  -- Ξ ⊢ w1 := f old_ps[γ1,x = pat,δ] : old_t[γ1,x = pat,δ] -- the case we are defining. can only be used if specialized.

  -- Ξ ⊢ rhs : old_t[γ1,x = pat,δ] [ α' ↦ w1[α']
                                -- , φ  ↦ w1[φ = i1, p = refl]
                                -- , ψ  ↦ w1[ψ = i1, q = refl]
                                -- ]
  -- Ξ ⊢ q2 := tr (i. Path X(η) (q i0) (p i)) φ q : Path X(η) (q i0) (p i1)
  -- Ξ ⊢ pat_rec[0] = pat : D η v
  -- Ξ ⊢ pat_rec[1] = trX q2 (φ ∧ ψ) x0 : D η v
  -- Ξ ⊢ pat-rec[i] := trX (\ j → p (i ∨ j)) (i ∨ φ) (trX (q2_f i) (ψ ∧ (φ ∨ ~ i)) t)

  -- Ξ ⊢ δ_f[1] = tr (i. Δ[γ1,x = pat_rec[i]]) (φ ∧ ψ) δ
  -- Ξ ⊢ w0 := f old_ps[γ1,x = pat_rec[1] ,δ_f[1]] : old_t[γ1,x = pat_rec[1],δ_f[1]]
  -- Ξ ⊢ rhs := tr (i. old_t[γ1,x = pat_rec[~i], δ_f[~i]]) (φ ∧ ψ) w0 -- TODO plus sides.

  interval <- elInf primInterval
  iz <- primIZero
  io <- primIOne
  tHComp <- primHComp
  tNeg <- primINeg
  let neg i = pure tNeg <@> i
  let min i j = cl primIMin <@> i <@> j
  let max i j = cl primIMax <@> i <@> j
  let
    old_tel = scTel old_sc
    old_ps' = AbsN (teleNames old_tel) $ fromSplitPatterns $ scPats old_sc
    old_ps = pure $ old_ps'
    old_ty = pure $ AbsN (teleNames old_tel) $ fromMaybe __IMPOSSIBLE__ $ scTarget old_sc
  -- old_tel = Γ(x: D η v)Δ
  -- Γ1, (x : D η v)  ⊢ delta = (δ : Δ)
    (gamma1x,delta') = splitTelescopeAt (size old_tel - blockingVarNo x) old_tel
    delta = pure $ AbsN (teleNames gamma1x) $ delta'
    gamma1_size = (size gamma1x - 1)
    (gamma1,ExtendTel dType' _) = splitTelescopeAt gamma1_size gamma1x

  old_sides <- forM old_ps' $ \ ps -> do
    let vs = iApplyVars ps
    let tm = Def f $ patternsToElims ps
    xs <- forM vs $ \ v ->
        -- have to reduce these under the appropriate substitutions, otherwise non-normalizing(?)
          fmap (var v,) . reduce $ (inplaceS v iz `applySubst` tm, inplaceS v io `applySubst` tm)
    return $ concatMap (\(v,(l,r)) -> [(tNeg `apply` [argN v],l),(v,r)]) xs
  let
    gamma1ArgNames = teleArgNames gamma1
    deltaArgNames = teleArgNames delta'
  (params,xTel,dT) <- addContext gamma1 $ do
    Right (IsData, d, ps, _is, _cs, _) <- runExceptT $ isDatatype Inductive dType'
    def <- getConstInfo d
    let dTy = defType def
    let Datatype{dataSort = s} = theDef def
    TelV tel _ <- telView dTy
    let params = AbsN (teleNames gamma1) ps
        xTel = AbsN (teleNames gamma1) (tel `apply` ps)

    dT <- runNamesT [] $ do
          s <- open $ AbsN (teleNames tel) s
          bindNArg (teleArgNames gamma1) $ \ g1 -> do
          bindNArg (teleArgNames $ unAbsN xTel) $ \ x -> do
          params <- pure params `applyN` (fmap unArg <$> g1)
          x      <- sequence x
          s <- s `applyN` (map (pure . unArg) $ params ++ x)
          pure $ El s $ Def d [] `apply` (params ++ x)
    return $ (params, xTel,dT)

  let
    xTelI = pure $ expTelescope interval <$> xTel
    xTelIArgNames = teleArgNames (unAbsN xTel) -- same names

  -- Γ1, φ, p, ψ, q, x0 ⊢ pat := trX p φ (trX q ψ x0)
  let trX' = bindNArg gamma1ArgNames $ \ g1 -> do
             bindNArg ([defaultArg "phi"] ++ xTelIArgNames) $ \ phi_p -> do
             bindNArg [defaultArg "x0"] $ \ x0 -> do
             param_args <- fmap (map (setHiding Hidden . fmap (unnamed . dotP))) $
               pure params `applyN` (fmap unArg <$> g1)
             (phi:p) <- sequence phi_p
             x0 <- sequence x0
             pure $ DefP defaultPatternInfo q_trX $ param_args ++ p ++ [phi] ++ x0
      trX = (fmap . fmap . fmap) patternToTerm <$> trX'
  let
    hcompD' g1 v =
        bindNArg [argH "psi",argN "u", argN "u0"] $ \ x0 -> do
        x0 <- sequence x0
        Just (LEl l t) <- (toLType =<<) $ pure dT `applyN` g1 `applyN` v
        let ty = map (fmap (unnamed . dotP) . argH) [Level l,t]
        pure $ DefP defaultPatternInfo q_hcomp $ ty ++ x0
  hcompD <- runNamesT [] $
            bindN (map unArg $ gamma1ArgNames) $ \ g1 -> do
            bindN (teleNames $ unAbsN $ xTel) $ \ v -> do
            fmap patternToTerm <$> hcompD' g1 v
  let pat' =
            bindN (map unArg gamma1ArgNames) $ \ g1 -> do
            bindN (map unArg $ ([defaultArg "phi"] ++ xTelIArgNames)) $ \ phi_p -> do
            bindN ["psi","u","u0"] $ \ x0 -> do
            let trX = trX' `applyN` g1
            let p0 = flip map (tail phi_p) $ \ p -> p <@> pure iz
            trX `applyN` phi_p `applyN` [hcompD' g1 p0 `applyN` x0]
      pat = (fmap . fmap . fmap) patternToTerm <$> pat'
  let deltaPat g1 phi p x0 =
        delta `applyN` (g1 ++ [pat `applyN` g1 `applyN` (phi:p) `applyN` x0])
  -- Ξ
  cTel <- runNamesT [] $
    abstractN (pure gamma1) $ \ g1 -> do
    abstractT "φ" (pure interval) $ \ phi -> do
    abstractN (xTelI `applyN` g1) $ \ p -> do
    let p0 = flip map p $ \ p -> p <@> pure iz
    let ty = pure dT `applyN` g1 `applyN` p0
    abstractT "ψ" (pure interval) $ \ psi -> do
    abstractT "u" (pure interval --> pPi' "o" psi (\ _ -> ty)) $ \ u -> do
    abstractT "u0" ty $ \ u0 -> do
    deltaPat g1 phi p [psi,u,u0]

  ps_ty_rhs <- runNamesT [] $ do
    bindN (map unArg gamma1ArgNames) $ \ g1 -> do
    bind "φ" $ \ phi -> do
    bindN (map unArg xTelIArgNames) $ \ p -> do
    bind "ψ" $ \ psi -> do
    bind "u" $ \ u -> do
    bind "u0" $ \ u0 -> do
    bindN (map unArg deltaArgNames) $ \ d -> do
    let
      x0 = [psi,u,u0]
      ps :: NamesT TCM NAPs
      ps = old_ps `applyN` (g1
                          ++ [pat' `applyN` g1 `applyN` (phi:p) `applyN` x0]
                          ++ d)

      rhsTy = old_ty `applyN` (g1
                          ++ [pat `applyN` g1 `applyN` (phi:p) `applyN` x0]
                          ++ d)

    xTel <- (open =<<) $ pure xTel `applyN` g1
    -- Ξ ⊢ pat-rec[i] := trX .. (hfill ... (~ i))
    pat_rec <- (open =<<) $ bind "i" $ \ i -> do
          let tr x = trX `applyN` g1 `applyN` (phi:p) `applyN` [x]
          let p0 = flip map p $ \ p -> p <@> pure iz
          tr (hcomp (pure dT `applyN` g1 `applyN` p0)
                    [(psi,lam "j" $ \ j -> u <@> (min j (neg i)))
                    ,(i  ,lam "j" $ \ _ -> ilam "o" $ \ _ -> u0)]
                    u0)
    --   args : (i.old_tel)  -> ...
    let mkBndry args = do
            args1 <- (mapM open =<<) $ (absApp <$> args <*> pure io)
            -- faces ought to be constant on "j"
            faces <- pure (fmap (map fst) old_sides) `applyN` args1
            us <- forM (sequence (fmap (map snd) old_sides)) $ \ u -> do
                  lam "j" $ \ j -> ilam "o" $ \ _ -> do
                    args <- (mapM open =<<) $ (absApp <$> args <*> j)
                    pure u `applyN` args
            forM (zip faces us) $ \ (phi,u) -> liftM2 (,) (open phi) (open u)
    rhs <- do
      d_f <- (open =<<) $ bind "j" $ \ j -> do
        tel <- bind "j" $ \ j -> delta `applyN` (g1 ++ [absApp <$> pat_rec <*> j])
        face <- pure iz
        j <- j
        d <- map defaultArg <$> sequence d
        Right d_f <- lift $ runExceptT $ trFillTel tel face d j
        pure $ map unArg d_f
      let args = bind "j" $ \ j -> do
            g1 <- sequence g1
            x <- absApp <$> pat_rec <*> neg j
            ys <- absApp <$> d_f <*> neg j
            pure $ g1 ++ x:ys
      ty <- (open =<<) $ bind "j" $ \ j -> do
           args <- (mapM open =<<) $ absApp <$> args <*> j
           fmap unDom $ old_ty `applyN` args
      let face = pure iz
      othersys <- (open =<<) $ lam "j" $ \ j -> ilam "o" $ \ _ -> do
        args' <- (mapM open =<<) $ absApp <$> args <*> j
        fmap (Def f) $ (fmap patternsToElims <$> old_ps) `applyN` args'
      sys <- mkBndry args
      let
        -- we could specialize all of sysphi/syspsi/base to compute
        -- away trX or the hcomp respectively, should lead to
        -- smaller/more efficient terms.
        --
        -- we could also ditch sysphi completely,
        -- as the computation rule for hcomp would achieve the same.
        sysphi = othersys
        syspsi = othersys
      base <- (open =<<) $ do
        args' <- (mapM open =<<) $ absApp <$> args <*> pure iz
        fmap (Def f) $ (fmap patternsToElims <$> old_ps) `applyN` args'
      transpSys ty ((phi,sysphi):(psi,syspsi):sys) face base
    (,,) <$> ps <*> rhsTy <*> pure rhs
  let (ps,ty,rhs) = unAbsN $ unAbs $ unAbs $ unAbs $ unAbsN $ unAbs $ unAbsN $ ps_ty_rhs
  reportSDoc "tc.cover.trx.hcomp" 20 $ "trX-hcomp clause for" <+> prettyTCM f
  let c = Clause { clauseTel = cTel
                  , namedClausePats = ps
                  , clauseBody = Just rhs
                  , clauseType = Just $ Arg (getArgInfo ty) (unDom ty)
                  , clauseLHSRange = noRange
                  , clauseFullRange = noRange
                  , clauseCatchall = False
                  , clauseRecursive = Just True
                  , clauseUnreachable = Just False
                  , clauseEllipsis = NoEllipsis
                  }
  debugClause "tc.cover.trx.hcomp" c
  return $ c
createMissingTrXConClause :: QName -- trX
                            -> QName -- f defined
                            -> Arg Nat
                            -> BlockingVar
                            -> SplitClause
                            -> QName -- constructor name
                            -> UnifyEquiv
                            -> TCM Clause
createMissingTrXConClause q_trX f n x old_sc c (UE gamma gamma' xTel u v rho tau leftInv) = do
  reportSDoc "tc.cover.trxcon" 20 $ "trX-con clause for" <+> prettyTCM f <+> "with con" <+> prettyTCM c
  reportSDoc "tc.cover.trxcon" 20 $ nest 2 $ vcat $
    [ "gamma" <+> prettyTCM gamma
    , "gamma'" <+> prettyTCM gamma'
    , "xTel" <+> addContext gamma (prettyTCM xTel)
    , "u"  <+> addContext gamma (prettyTCM u)
    , "v"  <+> addContext gamma (prettyTCM v)
    , "rho" <+> addContext gamma' (prettyTCM rho)
    ]

  Constructor{conSrcCon = chead} <- theDef <$> getConstInfo c

  -- = TheInfo $ UE delta1' eqTel (map unArg conIxs) (map unArg givenIxs) rho0 tau leftInv

  -- η : Params_D ⊢ c : (a : Args(η)) → D η (ξ(η,a))

  -- scTel old_sc = Γ1, (x : D η v), Δ
  -- Γ1, (x : D η v), Δ ⊢ f old_ps : old_t [α(γ1,x,δ) ↦ e(γ1,x,δ)]

  -- Γ = Γ1, a : Args(η)
  -- Γ ⊢ u = ξ(η,a)
  -- Γ ⊢ c a : D η u

  -- Γ' ⊢ ρ : Γ

  -- Γ' ⊢ u[ρ] = v[ρ] : X(η)[ρ]

  -- Γ' ⊢ c a[ρ] : (D η v)[ρ]

  -- Γ' ⊢ ρx := ρ,x = c a[ρ] : Γ,(x : D η v)

  -- Γ',Δ[ρx] ⊢ old_t[ρx]
  -- Γ',Δ[ρx] ⊢ f old_ps[ρx] : old_t[ρx] [α[ρx] ↦ e[γ1,x,δ][ρx]]

  -- Γ,(φ : I),(p : Path X(η) u v) ⊢ τ : Γ'

  -- Γ,(φ : I),(p : Path X(η) u v) ⊢ [ρx][τ] = [ρ[τ], x = c a[ρ[τ]]] : Γ,(x : D η v)

  -- Γ,(φ : I),(p : Path X(η) u v) ⊢ leftInv : ρ[τ],i1,refl ≡ idS : Γ,(φ : I),(p : Path X(η) u v)

  -- Γ,(φ : I),(p : Path X(η) u v)| (i : I) ⊢ leftInv i : Γ,(φ : I),(p : Path X(η) u v)

  -- Γ,(φ : I),(p : Path X(η) u v) ⊢ leftInv i0 = ρ[τ],i1,refl : Γ,(φ : I),(p : Path X(η) u v)
  -- Γ,(φ : I),(p : Path X(η) u v) ⊢ leftInv i1 = γ   ,φ ,p    : Γ,(φ : I),(p : Path X(η) u v)
  --                                 leftInv[φ = i1][i] = idS

  -- Γ,(φ : I),(p : Path X(η) u v),Δ[ρx][τ] ⊢ τ' = liftS |Δ[ρx]| τ : Γ',Δ[ρx]

  -- Γ,(φ : I),(p : Path X(η) u v),Δ[ρx][τ] ⊢
  --            w = f old_ps[γ1[ρ[τ]],x = c a[ρ[τ]],δ] : old_t[ρx][τ'] = old_t[γ1[ρ[τ]],x = c a[ρ[τ]],δ]

  -- Γ,(φ : I),(p : Path X(η) u v),Δ[ρx][τ], α(γ1,x,δ)[ρx][τ'] ⊢ w = e(γ1,x,δ)[ρx][τ']

  -- Γ,(φ : I),(p : Path X(η) u v) ⊢ pat := trX p φ (c a) : D η v


  -- Ξ = Γ,(φ : I),(p : Path X(η) u v),(δ : Δ[x = pat])

  -- Ξ ⊢ δ_f[1] = trTel (i. Δ[γ1[leftInv (~ i)], pat[leftInv (~i)]]) φ δ : Δ[ρ[τ], x = c a[ρ[τ]]]

  -- Ξ ⊢ w[δ_f[1]] : old_t[γ1[ρ[τ]],x = c a[ρ[τ]],δ_f[1]]
  -- Ξ, α(γ1,x,δ)[ρx][τ'][δ = δ_f[1]] ⊢ w[δ_f[1]] = e(γ1,x,δ)[ρx][τ'][δ_f[1]]

  -- Ξ, α(γ1[ρ[τ]],c a[ρ[τ]],δ_f[1]) ⊢ w[δ_f[1]] = e(γ1[ρ[τ]],c a[ρ[τ]],δ_f[1])

  -- Ξ ⊢ ?rhs : old_t[γ1,x = pat,δ] [α(γ1,pat,δ) ↦ e(γ1,pat,δ)
  --                               ,φ           ↦ w
  --                               ]

  -- ?rhs := transp (i. old_t[γ1[leftInv i],x = pat[leftInv i], δ_f[~i]]) φ (w[δ_f[1]])

  -- we shall consider α(γ1,pat,δ) = α(γ1[ρ[τ]],c a[ρ[τ]],δ_f[1])
  -- also rather than (p : Path X(η) u v) we'll have (p : I -> X(η)), same as the type of trX.

  iz <- primIZero
  interval <- elInf primInterval
  let
      old_tel = scTel old_sc
      old_ps = pure $ AbsN (teleNames old_tel) $ fromSplitPatterns $ scPats old_sc
      old_ty = pure $ AbsN (teleNames old_tel) $ fromMaybe __IMPOSSIBLE__ $ scTarget old_sc
  -- old_tel = Γ(x: D η v)Δ
  -- Γ1, (x : D η v)  ⊢ delta = (δ : Δ)
      (gamma1x,delta') = splitTelescopeAt (size old_tel - blockingVarNo x) old_tel
  let
    gammaArgNames = teleArgNames gamma
    deltaArgNames = teleArgNames delta'
  let
    xTelI = pure $ AbsN (teleNames gamma) $ expTelescope interval xTel
    delta = pure $ AbsN (teleNames gamma1x) $ delta'
    gamma1_size = (size gamma1x - 1)
    (gamma1,ExtendTel dType' _) = splitTelescopeAt gamma1_size gamma1x
  params <- addContext gamma1 $ do
    Right (IsData, _d, ps, _is, _cs, _) <- runExceptT $ isDatatype Inductive dType'
    return $ AbsN (teleNames gamma1) ps
  -- Γ, φ , p ⊢ pat := trX p φ (c a)
  let pat' =
            bindNArg gammaArgNames $ \ g1_args -> do
            bindNArg ([defaultArg "phi"] ++ teleArgNames xTel) $ \ phi_p -> do
            let (g1,args) = splitAt gamma1_size g1_args
            (phi:p) <- sequence phi_p
            args <- sequence args
            let cargs = defaultArg $ unnamed $ ConP chead noConPatternInfo args
            param_args <- fmap (map (setHiding Hidden . fmap (unnamed . dotP))) $
              pure params `applyN` take gamma1_size (fmap unArg <$> g1_args)
            pure $ DefP defaultPatternInfo q_trX $ param_args ++ p ++ [phi,cargs]
      pat = (fmap . fmap) patternToTerm <$> pat'
      pat_left' = (fmap . fmap) (Abs "i" . (applySubst leftInv)) <$> pat
      g1_left' = bindN (map unArg gammaArgNames) $ \ g1_args -> do
                bindN (map unArg $ [defaultArg "phi"] ++ teleArgNames xTel) $ \ phi_p -> do
                g1 <- sequence $ take gamma1_size g1_args :: NamesT TCM [Term]
                pure $ Abs "i" (applySubst leftInv g1)

  gamma <- return $ pure gamma
  let deltaPat g1_args phi p =
        delta `applyN` (take gamma1_size g1_args ++ [pat `applyN` g1_args `applyN` (phi:p)])
  let neg i = cl primINeg <@> i
  -- Ξ
  cTel <- runNamesT [] $
    abstractN gamma $ \ g1_args -> do
    abstractT "φ" (pure interval) $ \ phi -> do
    abstractN (xTelI `applyN` g1_args) $ \ p -> do
    deltaPat g1_args phi p
  ps_ty_rhs <- runNamesT [] $ do
    bindN (map unArg gammaArgNames) $ \ g1_args -> do
    bind "phi" $ \ phi -> do
    bindN (teleNames xTel) $ \ p -> do
    bindN (map unArg $ deltaArgNames) $ \ d -> do
    let
      g1_left = g1_left' `applyN` g1_args `applyN` (phi:p)
      pat_left = pat_left' `applyN` g1_args `applyN` (phi:p)
      g1 :: Vars TCM
      g1 = take gamma1_size g1_args

      args :: Vars TCM
      args = drop gamma1_size g1_args

      ps :: NamesT TCM NAPs
      ps = old_ps `applyN` (g1 ++ [pat' `applyN` g1_args `applyN` (phi:p)] ++ d)

      rhsTy = old_ty `applyN` (g1 ++ [pat `applyN` g1_args `applyN` (phi:p)] ++ d)

    -- (i. Δ[γ1[leftInv (~ i)], pat[leftInv (~i)]])
    delta_f <- (open =<<) $ bind "i" $ \ i -> do
      let ni = neg i
      dargs <- (mapM open =<<) $ do
        xs <- absApp <$> g1_left <*> ni
        y <- absApp <$> pat_left <*> ni
        return $ xs ++ [y]
      delta `applyN` dargs

    --  trFillTel (i. Δ[γ1[leftInv (~ i)], pat[leftInv (~i)]]) φ δ
    d_f <- (open =<<) $ bind "i" $ \ i -> do
      delta_f <- delta_f
      phi <- phi
      d <- map defaultArg <$> sequence d
      i <- i
      Right d_f <- lift $ runExceptT $ trFillTel delta_f phi d i
      pure $ map unArg d_f

    -- w = Def f (old_ps[g1_left[i],pat_left[i],d_f[~ i]])
    w <- (open =<<) $ bind "i" $ \ i -> do
      psargs <- (mapM open =<<) $ do
        xs <- absApp <$> g1_left <*> i
        y <- absApp <$> pat_left <*> i
        zs <- absApp <$> d_f <*> neg i
        return $ xs ++ [y] ++ zs
      ps <- (fmap patternsToElims <$> old_ps) `applyN` psargs
      pure $ Def f ps


    -- (i. old_t[γ1[leftInv i],x = pat[leftInv i], δ_f[~i]])
    ty <- (open =<<) $ bind "i" $ \ i -> do
      tyargs <- (mapM open =<<) $ do
        xs <- absApp <$> g1_left <*> i
        y <- absApp <$> pat_left <*> i
        zs <- absApp <$> d_f <*> neg i
        return $ xs ++ [y] ++ zs
      fmap unDom $ old_ty `applyN` tyargs

    sys <- do
      sides <- do
        neg <- primINeg
        io <- primIOne
        vs <- iApplyVars <$> ps
        tm <- w
        xs <- forM vs $ \ v ->
            -- have to reduce these under the appropriate substitutions, otherwise non-normalizing(?)
              fmap (var v,) . reduce $ (inplaceS v iz `applySubst` tm, inplaceS v io `applySubst` tm)
        return $ concatMap (\(v,(l,r)) -> [(neg `apply` [argN v],l),(v,r)]) xs
      forM sides $ \ (psi,u') -> do
        u' <- open u'
        u <- lam "i" $ \ i -> ilam "o" $ \ o -> absApp <$> u' <*> i
        (,) <$> open psi <*> open u

    let rhs = transpSys ty sys phi (absApp <$> w <*> pure iz)

    (,,) <$> ps <*> rhsTy <*> rhs

  let (ps,ty,rhs) = unAbsN $ unAbsN $ unAbs $ unAbsN $ ps_ty_rhs
  return $ Clause { clauseTel = cTel
                  , namedClausePats = ps
                  , clauseBody = Just rhs
                  , clauseType = Just $ Arg (getArgInfo ty) (unDom ty)
                  , clauseLHSRange = noRange
                  , clauseFullRange = noRange
                  , clauseCatchall = False
                  , clauseRecursive = Just True
                  , clauseUnreachable = Just False
                  , clauseEllipsis = NoEllipsis
                  }


-- | If given @TheInfo{}@ then assumes "x : Id u v" and
--   returns both a @SplittingDone@ for conId, and the @Clause@ that covers it.
createMissingConIdClause :: QName         -- ^ function being defined
                         -> Arg Nat       -- ^ @covSplitArg@ index
                         -> BlockingVar   -- ^ @x@ variable being split on.
                         -> SplitClause   -- ^ clause before split
                         -> IInfo         -- ^ info from unification
                         -> TCM (Maybe ((SplitTag,SplitTree),Clause))
createMissingConIdClause f _n x old_sc (TheInfo info) = setCurrentRange f $ do
  let
    -- iΓ'
    itel = infoTel
    -- with 3 params, reflId : Id A u u -- no arguments.
    -- iΓ' ⊢ iρ : Γ
    --
    -- Δ = Γ,φ,(p : u ≡ v) ⊢ iτ : iΓ'
    -- ρ = iρ
    -- τ = iτ
    irho = infoRho info
    itau = infoTau info
    ileftInv = infoLeftInv info
  interval <- elInf primInterval
  tTrans  <- primTrans
  tComp  <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinComp
  conId <- fromMaybe __IMPOSSIBLE__ <$> getName' builtinConId
  let bindSplit (tel1,tel2) = (tel1,AbsN (teleNames tel1) tel2)
  let
      old_tel = scTel old_sc

  -- old_tel = Γ(x: Id A u v)Δ
  -- Γ(x: Id A u v)Δ ⊢ old_t
  -- Γ ⊢ hdelta = (x : Id A u v)(δ : Δ)
      pair@(_gamma,_hdelta@(ExtendTel hdom delta)) = splitTelescopeAt (size old_tel - (blockingVarNo x + 1)) old_tel
      (gamma,hdelta) = bindSplit pair
      old_t  = AbsN (teleNames old_tel) $ fromJust $ scTarget old_sc
      old_ps = AbsN (teleNames old_tel) $ patternsToElims $ fromSplitPatterns $ scPats old_sc
      old_ps' = AbsN (teleNames old_tel) $ fromSplitPatterns $ scPats old_sc

  params <- runNamesT [] $ do
    hdelta <- open hdelta
    bindN (teleNames gamma) $ \ args -> do
       hdelta@(ExtendTel hdom _) <- applyN hdelta args
       Def _Id es@[_,_,_,_] <- reduce $ unEl $ unDom hdom
       return $ map unArg $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

  working_tel <- runNamesT [] $ do
    hdelta <- open hdelta
    params <- open params
    abstractN (pure gamma) $ \ args -> do
      pTel <- open =<< (lift $ pathTelescope (infoEqTel info) (map defaultArg $ infoEqLHS info) (map defaultArg $ infoEqRHS info))
      abstractN (pure (telFromList [defaultDom ("phi",interval)] :: Telescope)) $ \ [phi] ->
        abstractN pTel $ \ [p] -> do
          [l,bA,x,y] <- mapM open =<< applyN params args
          apply1 <$> applyN hdelta args <*> (cl primConId <#> l <#> bA <#> x <#> y <@> phi <@> p)
  -- working_tel ⊢ i. γ[leftInv i]
  (gamma_args_left :: Abs [Term], con_phi_p_left :: Abs Term) <- fmap (raise (size delta) . unAbsN) . runNamesT [] $ do
    params <- open params
    bindN (teleNames gamma ++ ["phi","p"]) $ \ args' -> do
      let (args,[phi,p]) = splitAt (size gamma) args'
      [l,bA,x,y] <- mapM open =<< applyN params args
      gargs <- Abs "i" . applySubst ileftInv <$> sequence args
      con_phi_p <- Abs "i" . applySubst ileftInv <$> do
        (cl primConId <#> l <#> bA <#> x <#> y <@> phi <@> p)
      return (gargs,con_phi_p)
  ps <- fmap unAbsN . runNamesT [] $ do
    old_ps' <- open $ old_ps'
    params <- open params
    bindN (teleNames working_tel) $ \ (wargs :: [NamesT TCM Term]) -> do
      let (g,phi:p:d) = splitAt (size gamma) $ telePatterns working_tel []
      params <- map (argH . unnamed . dotP) <$> applyN params (take (size gamma) wargs)
      let x = DefP defaultPatternInfo conId $ params ++ [phi,p]
      args <- open $ map namedArg g ++ [x] ++ map namedArg d
      applyN' old_ps' args
  -- tel = Γ',Δ[ρ,x = refl]
  -- Γ' ⊢ ρ : Γ
  -- Γ' ⊢ u[ρ] = v[ρ] : A[ρ]

  -- Γ' ⊢ ρ,x=refl : Γ,(x : Id A u v)

  -- Γ',Δ[ρ,x = refl] ⊢ old_t[ρ,x=refl] = Δ₂ -> t
  -- Γ',Δ[ρ,x = refl] ⊢ f old_ps[ρ,x = refl] : old_t[ρ,x = refl]
  -- Γ,(φ : I),(p : Path A u v) ⊢ τ : Γ'

  -- Γ' ⊢ [ρ,x = refl u[ρ]] : Γ,(x : Id A u v)

  -- Γ,(φ : I),(p : Path A u v) ⊢ [ρ,x = refl u[ρ]][τ] = [ρ[τ], x = refl u[ρ[τ]]] : Γ,(x : Id A u v)

  -- Γ,(φ : I),(p : Path A u v) ⊢ leftInv : ρ[τ],i1,refl ≡ idS : Γ,(φ : I),(p : Path A u v)

  -- Γ,(φ : I),(p : Path A u v)| (i : I) ⊢ leftInv i : Γ,(φ : I),(p : Path A u v)

  -- Γ,(φ : I),(p : Path A u v) ⊢ leftInv i0 = ρ[τ],i1,refl : Γ,(φ : I),(p : Path A u v)
  -- Γ,(φ : I),(p : Path A u v) ⊢ leftInv i1 = γ   ,φ ,p : Γ,(φ : I),(p : Path A u v)
  --                      leftInv[φ = i1][i] = idS

  -- Γ,(φ : I),(p : Path A u v),Δ[ρ,x = refl][τ] ⊢ τ' = liftS |Δ[ρ,x = refl]| τ : Γ',Δ[ρ,x = refl]

  -- Γ,(φ : I),(p : Path A u v),Δ[ρ,x = refl][τ] ⊢
  --            w = f old_ps[ρ[τ],x = refl u[ρ[τ]],δ] : old_t[ρ,x = refl][τ'] = old_t[ρ[τ],x = refl u[ρ[τ]],δ]

  -- Γ,(φ : I),(p : Path A u v) | (i : I) ⊢ μ = ⟨φ,p⟩[leftInv (~i)] : (Id A u v)[γ[leftInv (~ i)]]
  --                                     μ[0] = ⟨ φ             , p    ⟩
  --                                     μ[1] = ⟨ 1             , refl ⟩

  -- Γ,(φ : I),(p : Path A u v),(δ : Δ[x = ⟨ φ , p ⟩]) ⊢
  --         δ_f[1] = vecTransp (i. Δ[γ[leftInv (~ i)], ⟨φ,p⟩[leftInv (~i)]]) φ δ : Δ[ρ[τ], x = refl u[ρ[τ]]]

  -- Γ,(φ : I),(p : Path A u v),(δ : Δ[x = ⟨ φ , p ⟩]) ⊢ w[δ_f[1]] : old_t[ρ[τ],x = refl u[ρ[τ]],δ_f[1]]
  -- Γ,(φ : I),(p : Path A u v),Δ[x = ⟨ φ , p ⟩] ⊢ rhs = transp (i. old_t[γ[leftInv i],x = ⟨φ,p⟩[leftInv i], δ_f[~i]]) φ (w[δ_f[1]]) : old_t[γ,x = ⟨ φ , p ⟩,δ]
  let
      getLevel t = do
        s <- reduce $ getSort t
        case s of
          Type l -> pure (Level l)
          s      -> do
            reportSDoc "tc.cover.hcomp" 20 $ text "getLevel, s = " <+> prettyTCM s
            typeError . GenericDocError =<<
                    (text "The sort of" <+> prettyTCM t <+> text "should be of the form \"Set l\"")
  (ty,rhs) <- addContext working_tel $ runNamesT [] $ do
    let
        raiseFrom tel = raise (size working_tel - size tel)
        all_args = teleArgs working_tel :: Args
        (gamma_args,phi:p:delta_args) = splitAt (size gamma) all_args
    old_t <- open $ raiseFrom EmptyTel old_t
    old_ps <- open $ raiseFrom EmptyTel old_ps
    delta_args <- open delta_args
    gamma_args_left <- open gamma_args_left
    con_phi_p_left <- open con_phi_p_left
    hdelta <- open $ raiseFrom gamma hdelta
    delta_f <- bind "i" $ \ i -> do
      apply1 <$> applyN' hdelta (lazyAbsApp <$> gamma_args_left <*> (cl primINeg <@> i)) <*> (lazyAbsApp <$> con_phi_p_left <*> (cl primINeg <@> i))
    delta_f <- open delta_f
    [phi,p] <- mapM (open . unArg) [phi,p]
    delta_args_f <- bind "i" $ \ i -> do

      m <- trFillTel' True <$> delta_f <*> phi <*> delta_args <*> i
      either __IMPOSSIBLE__ id <$> (lift $ runExceptT m)
    delta_args_f <- open delta_args_f
    old_t_f <- (open =<<) $ bind "i" $ \ i -> do
      g <- lazyAbsApp <$> gamma_args_left <*> i
      x <- lazyAbsApp <$> con_phi_p_left <*> i
      d <- lazyAbsApp <$> delta_args_f <*> (cl primINeg <@> i)
      args <- open $ g ++ [x] ++ map unArg d
      applyN' old_t args
    w <- (open =<<) $ bind "i" $ \ i -> do
      g <- lazyAbsApp <$> gamma_args_left <*> i
      x <- lazyAbsApp <$> con_phi_p_left <*> i
      d <- lazyAbsApp <$> delta_args_f <*> (cl primINeg <@> i)
      args <- open $ g ++ [x] ++ map unArg d
      Def f <$> applyN' old_ps args

    ps <- open ps
    max <- primIMax
    iz <- primIZero
    alphas <- (open =<<) $ do
      vs <- iApplyVars <$> ps
      neg <- primINeg
      zero <- primIZero
      return $ foldr (\ x r -> max `apply` [argN $ max `apply` [argN x, argN (neg `apply` [argN x])], argN r]) zero $ map var vs
    sides <- (open =<<) $ do
      neg <- primINeg
      io <- primIOne
      bind "i" $ \ i -> do
        vs <- iApplyVars <$> ps
        tm <- lazyAbsApp <$> w <*> i
        xs <- forM vs $ \ v ->
          -- have to reduce these under the appropriate substitutions, otherwise non-normalizing
          fmap (var v,) . reduce $ (inplaceS v iz `applySubst` tm, inplaceS v io `applySubst` tm)
        phiv <- fromMaybe __IMPOSSIBLE__ . deBruijnView <$> phi
        -- extra assumption: phi |- w i = w 0, otherwise we need [ phi -> w 0 ] specifically
        tm_phi <- reduce $ inplaceS phiv io `applySubst` tm
        phi <- phi
        return $ (phi,tm_phi) : concatMap (\(v,(l,r)) -> [(neg `apply` [argN v],l),(v,r)]) xs

    imax <- return $ \ i j -> apply max . map argN $ [i,j]
    tPOr <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinPOr
    let
      pOr l ty phi psi u0 u1 = do
          [phi,psi] <- mapM open [phi,psi]
          pure tPOr <#> l
                    <@> phi <@> psi
                    <#> (ilam "o" $ \ _ -> ty) <@> noilam u0 <@> u1

      noilam u = do
         u <- open u
         ilam "o" $ \ _ -> u

      combine l ty [] = __IMPOSSIBLE__
      combine l ty [(psi,u)] = noilam u
      combine l ty ((psi,u):xs) = pOr l ty psi (foldr imax iz (map fst xs)) u (combine l ty xs)

    let ty i = lazyAbsApp <$> old_t_f <*> i
    l <- (open =<<) $ lam "i" $ \ i -> do
           t <- unDom <$> ty i
           lift $ getLevel t
    ((,) <$> ty (cl primIOne) <*>) $ do
         n <- length . unAbs <$> sides
         -- TODO don't comp if the family and the sides "j. [ α ↦ u ]" are constant?
         if n > 1 then
           pure tComp <#> l <@> (lam "i" $ \ i -> unEl . unDom <$> ty i)
                <@> (cl primIMax <@> phi <@> alphas)
                <@> (lam "i" $ \ i -> combine (l <@> i) (unEl . unDom <$> ty i) =<< (lazyAbsApp <$> sides <*> i))
                <@> (lazyAbsApp <$> w <*> primIZero)
         else
           pure tTrans <#> l <@> (lam "i" $ \ i -> unEl . unDom <$> ty i)
                <@> phi
                <@> (lazyAbsApp <$> w <*> primIZero)

  reportSDoc "tc.cover.conid" 20 $ text "conid case for" <+> text (show f)
  reportSDoc "tc.cover.conid" 20 $ text "tel =" <+> prettyTCM working_tel
  reportSDoc "tc.cover.conid" 25 $ addContext working_tel $ prettyTCM rhs

  let cl =   Clause { clauseLHSRange  = noRange
                    , clauseFullRange = noRange
                    , clauseTel       = working_tel
                    , namedClausePats = ps
                    , clauseBody      = Just $ rhs
                    , clauseType      = Just $ Arg (domInfo ty) (unDom ty)
                    , clauseCatchall  = False
                    , clauseUnreachable = Just False  -- missing, thus, not unreachable
                    , clauseRecursive = Just False
                    , clauseEllipsis = NoEllipsis
                    }
  addClauses f [cl]
  return $ Just ((SplitCon conId,SplittingDone (size working_tel)),cl)
createMissingConIdClause f n x old_sc NoInfo = return Nothing


{-
  OLD leftInv case
  -- Γ,(φ : I),(p : Path A u v) ⊢ leftInv : ρ[τ] ≡ wkS 2 : Γ
  -- Γ,(φ : I),(p : Path A u v)(i : I) ⊢ leftInv i : Γ
  -- Γ,(φ : I),(p : Path A u v) ⊢ leftInv i0 = ρ[τ] : Γ
  -- Γ,(φ : I),(p : Path A u v) ⊢ leftInv i1 = wkS 2 : Γ
  -- leftInv[φ = i1][i] = wkS 2

  -- Γ,(φ : I),(p : Path A u v),Δ[ρ,x = refl][τ] ⊢ τ' = liftS |Δ[ρ,x = refl]| τ : Γ',Δ[ρ,x = refl]

  -- Γ,(φ : I),(p : Path A u v),Δ[ρ,x = refl][τ] ⊢ w = f old_ps[ρ,x = refl][τ'] : old_t[ρ,x = refl][τ']

  -- Γ,(φ : I),(p : Path A u v) | (i : I) ⊢ μ = ⟨ (φ ∨ ~ i) , (\ j → p (i ∧ j)) ⟩ : Id A u (p i) =?= (Id A u v)[leftInv (~ i)]
                                  μ[0] = ⟨ 1 , (\ _ → u[ρ[τ]]) ⟩
                                  μ[1] = ⟨ φ , p               ⟩
  -- Γ,(φ : I),(p : Path A u v),(δ : Δ[x = ⟨ φ , p ⟩]) ⊢ vecTransp (i. Δ[leftInv (~ i),μ[i]]) φ δ : Δ[ρ[τ], x = refl u[ρ[τ]]]
-}

-- | Append an hcomp clause to the clauses of a function.
createMissingHCompClause
  :: QName
       -- ^ Function name.
  -> Arg Nat -- ^ index of hcomp pattern
  -> BlockingVar -- ^ Blocking var that lead to hcomp split.
  -> SplitClause -- ^ Clause before the hcomp split
  -> SplitClause
       -- ^ Clause to add.
   -> TCM Clause
createMissingHCompClause f n x old_sc (SClause tel ps _sigma' _cps (Just t)) = setCurrentRange f $ do
  reportSDoc "tc.cover.hcomp" 20 $ addContext tel $ text "Trying to create right-hand side of type" <+> prettyTCM t
  reportSDoc "tc.cover.hcomp" 30 $ addContext tel $ text "ps = " <+> prettyTCMPatternList (fromSplitPatterns ps)
  reportSDoc "tc.cover.hcomp" 30 $ text "tel = " <+> prettyTCM tel

  io      <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinIOne
  iz      <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinIZero
  let
    cannotCreate doc t = do
      typeError . SplitError $ CannotCreateMissingClause f (tel,fromSplitPatterns ps) doc t
  let old_ps = patternsToElims $ fromSplitPatterns $ scPats old_sc
      old_t  = fromJust $ scTarget old_sc
      old_tel = scTel old_sc
      -- old_tel = Γ(x:H)Δ
      -- Γ(x:H)Δ ⊢ old_t
      -- vs = iApplyVars old_ps
      -- [ α ⇒ b ] = [(i,f old_ps (i=0),f old_ps (i=1)) | i <- vs]

      -- Γ(x:H)(δ : Δ) ⊢ [ α ⇒ b ]
      -- Γ(x:H)Δ ⊢ f old_ps : old_t [ α ⇒ b ]
      -- Γ,φ,u,u0,Δ(x = hcomp φ u u0) ⊢ rhs_we_define : (old_t[ α ⇒ b ])(x = hcomp φ u u0)

      -- Extra assumption:
      -- tel = Γ,φ,u,u0,Δ(x = hcomp φ u u0),Δ'
      -- ps = old_ps[x = hcomp φ u u0],ps'
      -- with Δ' and ps' introduced by fixTarget.
      -- So final clause will be:
      -- tel ⊢ ps ↦ rhs_we_define{wkS ..} ps'
      getLevel t = do
        s <- reduce $ getSort t
        case s of
          Type l -> pure (Level l)
          s      -> do
            reportSDoc "tc.cover.hcomp" 20 $ text "getLevel, s = " <+> prettyTCM s
            typeError . GenericDocError =<<
                    (text "The sort of" <+> prettyTCM t <+> text "should be of the form \"Set l\"")

      -- Γ ⊢ hdelta = (x : H)(δ : Δ)
      (gamma,hdelta@(ExtendTel hdom delta)) = splitTelescopeAt (size old_tel - (blockingVarNo x + 1)) old_tel

      -- Γ,φ,u,u0,Δ(x = hcomp φ u u0) ⊢
      (working_tel,_deltaEx) = splitTelescopeAt (size gamma + 3 + size delta) tel

      -- Γ,φ,u,u0,(x:H)(δ : Δ) ⊢ rhoS : Γ(x:H)(δ : Δ)
      {- rhoS = liftS (size hdelta) $ raiseS 3 -}
      vs = iApplyVars (scPats old_sc)

  -- Γ(x:H)(δ : Δ) ⊢ [ α ⇒ b ] = [(i,f old_ps (i=0),f old_ps (i=1)) | i <- vs]
  alphab <- forM vs $ \ i -> do
               let
                 -- Γ(x:H)(δ : Δ) ⊢
                 tm = Def f old_ps
               -- TODO only reduce IApply _ _ (0/1), as to avoid termination problems
               (l,r) <- reduce (inplaceS i iz `applySubst` tm, inplaceS i io `applySubst` tm)
               return $ (var i, (l, r))



  cl <- do
    (ty,rhs) <- addContext working_tel $ do
      -- Γ(x:H)Δ ⊢ g = f old_ps : old_t [ α ⇒ b ]
      -- Γ(x:H)(δ : Δ) ⊢ [ α ⇒ b ]
      -- Γ,φ,u,u0 ⊢ Δf = i.Δ[x = hfill φ u u0 i]
      -- Γ,φ,u,u0,δ : Δ(x = hcomp φ u u0) ⊢ δ_fill     = i.tFillTel (i. Δf[~i]) δ (~ i) : i.Δf[i]
      -- Γ,φ,u,u0,δ : Δ(x = hcomp φ u u0) ⊢ old_t_fill = i.old_t[x = hfill φ u u0 i, δ_fill[i]]
      -- Γ,φ,u,u0,δ : Δ(x = hcomp φ u u0) ⊢ comp (\ i. old_t_fill[i])
      --                 (\ i. [ φ ↦ g[x = hfill φ u u0 i,δ_fill[i]] = g[u i,δ_fill[i]]
      --                         α ↦ b[x = hfill φ u u0 i,δ_fill[i]]
      --                        ])
      --                 (g[x = u0,δ_fill[0]]) : old_t[x = hcomp φ u u0,δ]

      runNamesT [] $ do
          tPOr <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinPOr
          tIMax <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinIMax
          tIMin <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinIMin
          tINeg <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinINeg
          tHComp <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinHComp
          tTrans <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinTrans
          extra_ps <- open $ patternsToElims $ fromSplitPatterns $ drop (length old_ps) ps
          let
            ineg j = pure tINeg <@> j
            imax i j = pure tIMax <@> i <@> j
            trFillTel' a b c d = do
              m <- trFillTel <$> a <*> b <*> c <*> d
              x <- lift $ runExceptT m
              case x of
                Left bad_t -> cannotCreate "Cannot transport with type family:" bad_t
                Right args -> return args
          comp <- do
            let forward la bA r u = pure tTrans <#> lam "i" (\ i -> la <@> (i `imax` r))
                                              <@> lam "i" (\ i -> bA <@> (i `imax` r))
                                              <@> r
                                              <@> u
            return $ \ la bA phi u u0 ->
              pure tHComp <#> (la <@> pure io) <#> (bA <@> pure io) <#> phi
                        <@> lam "i" (\ i -> ilam "o" $ \ o ->
                                forward la bA i (u <@> i <..> o))
                        <@> forward la bA (pure iz) u0
          let
            hcomp la bA phi u u0 = pure tHComp <#> la <#> bA
                                               <#> phi
                                               <@> u
                                               <@> u0

            hfill la bA phi u u0 i = hcomp la bA
                                               (pure tIMax <@> phi <@> (pure tINeg <@> i))
                                               (lam "j" $ \ j -> pure tPOr <#> la <@> phi <@> (pure tINeg <@> i) <#> ilam "o" (\ _ -> bA)
                                                     <@> ilam "o" (\ o -> u <@> (pure tIMin <@> i <@> j) <..> o)
                                                     <@> ilam "o" (\ _ -> u0)
                                                   )
                                               u0
          -- Γ,φ,u,u0,(δ : Δ(x = hcomp φ u u0)) ⊢ hcompS : Γ(x:H)(δ : Δ)
          hcompS <- lift $ do
            hdom <- pure $ raise 3 hdom
            let
              [phi,u,u0] = map (pure . var) [2,1,0]
              htype = pure $ unEl . unDom $ hdom
              lvl = getLevel $ unDom hdom
            hc <- pure tHComp <#> lvl <#> htype
                                      <#> phi
                                      <@> u
                                      <@> u0
            return $ liftS (size delta) $ hc `consS` raiseS 3
          -- Γ,φ,u,u0,Δ(x = hcomp phi u u0) ⊢ raise 3+|Δ| hdom
          hdom <- pure $ raise (3+size delta) hdom
          htype <- open $ unEl . unDom $ hdom
          lvl <- open =<< (lift . getLevel $ unDom hdom)

          -- Γ,φ,u,u0,Δ(x = hcomp phi u u0) ⊢
          [phi,u,u0] <- mapM (open . raise (size delta) . var) [2,1,0]
          -- Γ,x,Δ ⊢ f old_ps
          -- Γ ⊢ abstract hdelta (f old_ps)
          g <- open $ raise (3+size delta) $ abstract hdelta (Def f old_ps)
          old_t <- open $ raise (3+size delta) $ abstract hdelta (unDom old_t)
          let bapp a x = lazyAbsApp <$> a <*> x
          (delta_fill :: NamesT TCM (Abs Args)) <- (open =<<) $ do
            -- Γ,φ,u,u0,Δ(x = hcomp phi u u0) ⊢ x.Δ
            delta <- open $ raise (3+size delta) delta
            -- Γ,φ,u,u0,Δ(x = hcomp phi u u0) ⊢ i.Δ(x = hfill phi u u0 (~ i))
            deltaf <- open =<< bind "i" (\ i ->
                           (delta `bapp` hfill lvl htype phi u u0 (ineg i)))
            -- Γ,φ,u,u0,Δ(x = hcomp phi u u0) ⊢ Δ(x = hcomp phi u u0) = Δf[0]
            args <- (open =<<) $ teleArgs <$> (lazyAbsApp <$> deltaf <*> pure iz)
            bind "i" $ \ i -> addContext ("i" :: String) $ do -- for error messages.
              -- Γ,φ,u,u0,Δ(x = hcomp phi u u0),(i:I) ⊢ ... : Δ(x = hfill phi u u0 i)
              trFillTel' deltaf (pure iz) args (ineg i)
          let
            apply_delta_fill i f = apply <$> f <*> (delta_fill `bapp` i)
            call v i = apply_delta_fill i $ g <@> v
          ty <- do
                return $ \ i -> do
                    v <- hfill lvl htype phi u u0 i
                    hd <- old_t
                    args <- delta_fill `bapp` i
                    lift $ piApplyM hd $ Arg (domInfo hdom) v : args
          ty_level <- do
            t <- bind "i" ty
            s <- reduce $ getSort (absBody t)
            reportSDoc "tc.cover.hcomp" 20 $ text "ty_level, s = " <+> prettyTCM s
            case s of
              Type l -> open =<< lam "i" (\ _ -> pure $ Level l)
              _      -> cannotCreate "Cannot compose with type family:" =<< liftTCM (buildClosure t)

          let
            pOr_ty i phi psi u0 u1 = pure tPOr <#> (ty_level <@> i)
                                               <@> phi <@> psi
                                               <#> ilam "o" (\ _ -> unEl <$> ty i) <@> u0 <@> u1
          alpha <- do
            vars <- mapM (open . applySubst hcompS . fst) alphab
            return $ foldr (imax . (\ v -> v `imax` ineg v)) (pure iz) vars

          -- Γ,φ,u,u0,Δ(x = hcomp φ u u0) ⊢ b : (i : I) → [α] -> old_t[x = hfill φ u u0 i,δ_fill[i]]
          b <- do
             sides <- forM alphab $ \ (psi,(side0,side1)) -> do
                psi <- open $ hcompS `applySubst` psi

                [side0,side1] <- mapM (open . raise (3+size delta) . abstract hdelta) [side0,side1]
                return $ (ineg psi `imax` psi, \ i -> pOr_ty i (ineg psi) psi (ilam "o" $ \ _ -> apply_delta_fill i $ side0 <@> hfill lvl htype phi u u0 i)
                                                            (ilam "o" $ \ _ -> apply_delta_fill i $ side1 <@> hfill lvl htype phi u u0 i))
             let recurse []           i = __IMPOSSIBLE__
                 recurse [(psi,u)]    i = u i
                 recurse ((psi,u):xs) i = pOr_ty i psi (foldr (imax . fst) (pure iz) xs) (u i) (recurse xs i)
             return $ recurse sides

          ((,) <$> ty (pure io) <*>) $ do
            comp ty_level
               (lam "i" $ fmap unEl . ty)
                           (phi `imax` alpha)
                           (lam "i" $ \ i ->
                               let rhs = (ilam "o" $ \ o -> call (u <@> i <..> o) i)
                               in if null alphab then rhs else
                                   pOr_ty i phi alpha rhs (b i)
                           )
                           (call u0 (pure iz))
    reportSDoc "tc.cover.hcomp" 20 $ text "old_tel =" <+> prettyTCM tel
    let n = size tel - (size gamma + 3 + size delta)
    reportSDoc "tc.cover.hcomp" 20 $ text "n =" <+> text (show n)
    (TelV deltaEx t,bs) <- telViewUpToPathBoundary' n ty
    rhs <- pure $ raise n rhs `applyE` teleElims deltaEx bs

    cxt <- getContextTelescope
    reportSDoc "tc.cover.hcomp" 30 $ text "cxt = " <+> prettyTCM cxt
    reportSDoc "tc.cover.hcomp" 30 $ text "tel = " <+> prettyTCM tel
    reportSDoc "tc.cover.hcomp" 20 $ addContext tel $ text "t = " <+> prettyTCM t
    reportSDoc "tc.cover.hcomp" 20 $ addContext tel $ text "rhs = " <+> prettyTCM rhs

    return $ Clause { clauseLHSRange  = noRange
                    , clauseFullRange = noRange
                    , clauseTel       = tel
                    , namedClausePats = fromSplitPatterns ps
                    , clauseBody      = Just $ rhs
                    , clauseType      = Just $ defaultArg t
                    , clauseCatchall  = False
                    , clauseRecursive   = Nothing     -- TODO: can it be recursive?
                    , clauseUnreachable = Just False  -- missing, thus, not unreachable
                    , clauseEllipsis  = NoEllipsis
                    }
  addClauses f [cl]  -- Important: add at the end.
  return cl
createMissingHCompClause _ _ _ _ (SClause _ _ _ _ Nothing) = __IMPOSSIBLE__

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
                  , clauseCatchall  = False
                  , clauseRecursive   = Nothing     -- could be recursive
                  , clauseUnreachable = Just False  -- missing, thus, not unreachable
                  , clauseEllipsis  = NoEllipsis
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
        Record{recPars = np, recConHead = con, recInduction = i}
          | i == Just CoInductive && ind /= CoInductive ->
              throw CoinductiveDatatype
          | otherwise ->
              return (IsRecord, d, args, [], [conName con], False)
        _ -> throw NotADatatype
    _ -> throw NotADatatype

-- | Update the target type of the split clause after a case split.
fixTargetType :: SplitClause -> Dom Type -> TCM SplitClause
fixTargetType sc@SClause{ scTel = sctel, scSubst = sigma } target = do
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
    return $ sc { scTarget = Just $ applySplitPSubst sigma target }


-- | Add more patterns to split clause if the target type is a function type.
--   Returns the domains of the function type (if any).
insertTrailingArgs :: SplitClause -> TCM (Telescope, SplitClause)
insertTrailingArgs sc@SClause{ scTel = sctel, scPats = ps, scSubst = sigma, scCheckpoints = cps, scTarget = target } =
  caseMaybe target (return (empty,sc)) $ \ a -> do
    (TelV tel b) <- telViewUpTo (-1) $ unDom a
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
        newTarget = Just $ a $> b
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
    -- Get the type of the datatype
  -- Δ1 ⊢ dtype
  dsort <- liftTCM $ (parallelS (reverse $ map unArg pars) `applySubst`) . dataSort . theDef <$> getConstInfo d
  hCompName <- fromMaybe __IMPOSSIBLE__ <$> getPrimitiveName' builtinHComp
  theHCompT <- defType <$> getConstInfo hCompName
  let
    dlvl = Level . (\ (Type s) -> s) $ dsort
    dterm = Def d [] `apply` (pars ++ ixs)
  -- Δ1 ⊢ gamma
  TelV gamma _ <- lift $ telView (theHCompT `piApply` [setHiding Hidden $ defaultArg $ dlvl , defaultArg $ dterm])
  case (delta1 `abstract` gamma,IdS) of
    (delta1',rho0) -> do
--      debugSubst "rho0" rho0

      -- We have Δ₁' ⊢ ρ₀ : Δ₁Γ, so split it into the part for Δ₁ and the part for Γ
      let (rho1,rho2) = splitS (size gamma) $ toSplitPSubst rho0

      -- Andreas, 2015-05-01  I guess it is fine to use no @conPType@
      -- as the result of splitting is never used further down the pipeline.
      -- After splitting, Agda reloads the file.
      -- Andreas, 2017-09-03, issue #2729: remember that pattern was generated by case split.
      let
          -- cpi  = noConPatternInfo{ conPRecord = Just PatOSplit }
          -- conp = ConP con cpi $ applySubst rho2 $
          --          map (mapArgInfo hiddenInserted) $ tele2NamedArgs gamma0 gamma
          -- -- Andreas, 2016-09-08, issue #2166: use gamma0 for correct argument names
          defp = DefP defaultPatternInfo hCompName . map (setOrigin Inserted) $
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


data UnifyEquiv = UE { infoTel0 :: Telescope          -- Γ0
                     , infoTel :: Telescope           -- Γ'
                     , infoEqTel :: Telescope         -- Γ0 ⊢ Δ
                     , infoEqLHS :: [Term]            -- Γ0 ⊢ us : Δ
                     , infoEqRHS :: [Term]            -- Γ0 ⊢ vs : Δ
                     , infoRho :: PatternSubstitution -- Γ' ⊢ ρ : Γ0
                                                      -- Γ = Γ0,(φ : I),(eqs : Paths Δ us vs)
                                                      -- Γ' ⊢ ρ,i1,refls : Γ
                     , infoTau :: Substitution        -- Γ  ⊢ τ           : Γ'
                     , infoLeftInv :: Substitution    -- Γ | (i : I) ⊢ leftInv : Γ
                     -- leftInv[i=0] = ρ[τ],i1s,refls
                     -- leftInv[i=1] = idS
                     }
                  deriving Show

data IInfo = TheInfo UnifyEquiv | NoInfo deriving Show

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
    (TelV gamma0 (El _ d), boundary) <- liftTCM $ telViewPathBoundaryP (ctype `piApply` pars)
    let Def _ es = d
        Just cixs = allApplyElims es
    return (gamma0, cixs, boundary)

  -- Andreas, 2012-02-25 preserve name suggestion for recursive arguments
  -- of constructor

  let preserve (x, t@(El _ (Def d' _))) | d == d' = (n, t)
      preserve (x, t) = (x, t)
      gamma  = telFromList . map (fmap preserve) . telToList $ gamma0
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
  dtype <- do
         let (_, Dom{domInfo = info} : _) = splitAt (size tel - hix - 1) (telToList tel)
         let updCoh = composeCohesion (getCohesion info)
         TelV dtel dt <- telView dtype
         return $ abstract (mapCohesion updCoh <$> dtel) dt

  r <- unifyIndices'
         delta1Gamma
         flex
         (raise (size gamma) dtype)
         conIxs
         givenIxs

  TelV eqTel _ <- telView $ (raise (size gamma) dtype)

  case r of
    NoUnify {} -> debugNoUnify $> Nothing

    DontKnow errs -> do
      debugCantSplit
      throwError $ UnificationStuck (conName con) (delta1 `abstract` gamma) conIxs givenIxs errs
    Unifies (delta1',rho0,eqs,tauInv) -> do

      let unifyInfo | True -- moved the check higher up: Just d == mid -- here because we only handle Id for now.
                    , not $ null $ conIxs -- no point propagating this info if trivial?
                    , Right (tau,leftInv) <- tauInv
                    -- we report warning below if Left Illegal.
            = TheInfo $ UE delta1Gamma delta1' eqTel (map unArg conIxs) (map unArg givenIxs) rho0 tau leftInv
                    | otherwise
            = NoInfo

      when (isLeft tauInv) $
        -- TODO better error msg.
        lift $ genericWarning =<< text "No equiv while splitting on indexed family"

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
  where sc = SClause tel (toSplitPatterns ps) empty empty Nothing

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
        cons <- case checkEmpty of
          CheckEmpty   -> ifM (liftTCM $ inContextOfT $ isEmptyType $ unDom t) (pure []) (pure cons')
          NoCheckEmpty -> pure cons'
        mns  <- forM cons $ \ con -> fmap (SplitCon con,) <$>
          computeNeighbourhood delta1 n delta2 d pars ixs x tel ps cps con
        hcompsc <- if (isHIT || size ixs > 0) && inserttrailing == DoInsertTrailing
                   then computeHCompSplit delta1 n delta2 d pars ixs x tel ps cps
                   else return Nothing
        return ( dr
               , not (null ixs) -- Is "d" indexed?
               , catMaybes (mns ++ [fmap (fmap (,NoInfo)) hcompsc | not $ null $ catMaybes mns])
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
        return (IsData, False, map ((fmap (,NoInfo))) $ ns ++ [ ca ])

  (dr, isIndexed, ns) <- if null pcons' && not (null plits)
        then computeLitNeighborhoods
        else computeNeighborhoods

  ns <- case target of
    Just a  -> forM ns $ \ (con,(sc,info)) -> lift $ (con,) . (,info) <$> fixTargetType sc a
    Nothing -> return ns

  ns <- case inserttrailing of
    DontInsertTrailing -> return ns
    DoInsertTrailing   -> lift $ forM ns $ \(con,(sc,info)) ->
      (con,) . (,info) . snd <$> insertTrailingArgs sc

  -- Andreas, 2018-10-27, issue #3324; use isPropM.
  -- Need to reduce sort to decide on Prop.
  -- Cannot split if domain is a Prop but target is relevant.
  propArrowRel <- isPropM t `and2M`
    maybe (return True) (not <.> isPropM) target

  mHCompName <- getPrimitiveName' builtinHComp
  withoutK   <- collapseDefault . optWithoutK <$> pragmaOptions

  erased <- asksTC hasQuantity0
  reportSLn "tc.cover.split" 60 $ "We are in erased context = " ++ show erased
  let erasedError causedByWithoutK =
        throwError . ErasedDatatype causedByWithoutK =<<
          do liftTCM $ inContextOfT $ buildClosure (unDom t)
  case ns of
    []  -> do
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

    -- Jesper, 2018-05-24: If the datatype is in Prop we can
    -- only do empty splits, unless the target is in Prop too.
    (_ : _) | dr == IsData && propArrowRel ->
      throwError . IrrelevantDatatype =<< do liftTCM $ inContextOfT $ buildClosure (unDom t)

    -- Andreas, 2018-10-17: If more than one constructor matches, we cannot erase.
    (_ : _ : _) | not erased && not (usableQuantity t) ->
      erasedError False

    -- If exactly one constructor matches and the K rule is turned
    -- off, then we only allow erasure for non-indexed data types
    -- (#4172).
    [_] | not erased && not (usableQuantity t) &&
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

      liftTCM $ checkSortOfSplitVar dr (unDom t) target
      return $ Right $ Covering (lookupPatternVar sc x) ns

  where
    inContextOfT, inContextOfDelta2 :: (MonadTCM tcm, MonadAddContext tcm, MonadDebug tcm) => tcm a -> tcm a
    inContextOfT      = addContext tel . escapeContext __IMPOSSIBLE__ (x + 1)
    inContextOfDelta2 = addContext tel . escapeContext __IMPOSSIBLE__ x

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
                fieldSub = reverse (map unArg vs ++ prevFields) ++# EmptyS __IMPOSSIBLE__
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

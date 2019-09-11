{-# LANGUAGE NondecreasingIndentation #-}

{-| Coverage checking, case splitting, and splitting for refine tactics.

 -}

module Agda.TypeChecking.Coverage
  ( SplitClause(..), clauseToSplitClause, fixTarget
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
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Names
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.Primitive.Cubical (trFillTel)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin

import Agda.TypeChecking.Rules.LHS (checkSortOfSplitVar)
import Agda.TypeChecking.Rules.LHS.Problem (allFlexVars)
import Agda.TypeChecking.Rules.LHS.Unify

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
  , MonadError(throwError)
  , runExceptT
  )
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Size

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
  , scTarget :: Maybe (Arg Type)
    -- ^ The type of the rhs, living in context 'scTel'.
    --   This invariant is broken before calls to 'fixTarget';
    --   there, 'scTarget' lives in the old context.
    --   'fixTarget' moves 'scTarget' to the new context by applying
    --   substitution 'scSubst'.
  }

-- | A @Covering@ is the result of splitting a 'SplitClause'.
data Covering = Covering
  { covSplitArg     :: Arg Nat
     -- ^ De Bruijn level (counting dot patterns) of argument we split on.
  , covSplitClauses :: [(SplitTag, SplitClause)]
      -- ^ Covering clauses, indexed by constructor/literal these clauses share.
  }

-- | Project the split clauses out of a covering.
splitClauses :: Covering -> [SplitClause]
splitClauses (Covering _ qcs) = map snd qcs

-- | Create a split clause from a clause in internal syntax. Used by make-case.
clauseToSplitClause :: Clause -> SplitClause
clauseToSplitClause cl = SClause
  { scTel    = clauseTel cl
  , scPats   = toSplitPatterns $ namedClausePats cl
  , scSubst  = idS  -- Andreas, 2014-07-15  TODO: Is this ok?
  , scCheckpoints = Map.empty -- #2996: not __IMPOSSIBLE__ for debug printing
  , scTarget = clauseType cl
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
  let sc = SClause gamma xs idS checkpoints $ Just $ defaultArg a

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
  noex <- return $ List.filter (< length cs) $ Set.toList noex

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
                      , clauseUnreachable = Just False
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
        let unreachable = i `Set.notMember` used in
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
  CoverResult { coverMissingClauses = missing } <- cover f cs sc
  return $ null missing

data CoverResult = CoverResult
  { coverSplitTree       :: SplitTree
  , coverUsedClauses     :: Set Nat
  , coverMissingClauses  :: [(Telescope, [NamedArg DeBruijnPattern])]
  , coverPatterns        :: [Clause]
  -- ^ The set of patterns used as cover.
  , coverNoExactClauses  :: Set Nat
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
    , nest 2 $ "tel  =" <+> prettyTCM tel
    , nest 2 $ "ps   =" <+> do addContext tel $ prettyTCMPatternList $ fromSplitPatterns ps
    , nest 2 $ "target =" <+> do addContext tel $ maybe (text "<none>") prettyTCM target
    , nest 2 $ "target sort =" <+> do addContext tel $ maybe (text "<none>") (prettyTCM . getSort . unArg) target
    ]
  match cs ps >>= \case
    Yes (i,mps) -> do
      exact <- allM (map snd mps) isTrivialPattern
      let cl0 = indexWithDefault __IMPOSSIBLE__ cs i
      let noExactClause = if exact || clauseCatchall (indexWithDefault __IMPOSSIBLE__ cs i)
                          then Set.empty
                          else Set.singleton i
      reportSLn "tc.cover.cover" 10 $ "pattern covered by clause " ++ show i
      reportSDoc "tc.cover.cover" 20 $ text "with mps = " <+> do addContext tel $ pretty $ mps
      cl <- applyCl sc cl0 mps
      return $ CoverResult (SplittingDone (size tel)) (Set.singleton i) [] [cl] noExactClause

    No        ->  do
      reportSLn "tc.cover" 20 $ "pattern is not covered"
      -- TODO Andrea: add hcomp clause!
      case fmap getHiding target of
        Just h | isInstance h -> do
          -- Ulf, 2016-10-31: For now we only infer instance clauses. It would
          -- make sense to do it also for hidden, but since the value of a
          -- hidden clause is expected to be forced by later clauses, it's too
          -- late to add it now. If it was inferrable we would have gotten a
          -- type error before getting to this point.
          cl <- inferMissingClause f sc
          return $ CoverResult (SplittingDone (size tel)) Set.empty [] [cl] Set.empty
        _ -> do
          let ps' = fromSplitPatterns ps
          return $ CoverResult (SplittingDone (size tel)) Set.empty [(tel, ps')] [] Set.empty

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
    applyCl SClause{scTel = tel, scCheckpoints = cps} cl mps = addContext tel $ do
        reportSDoc "tc.cover.applyCl" 40 $ "applyCl"
        reportSDoc "tc.cover.applyCl" 40 $ "tel    =" <+> prettyTCM tel
        reportSDoc "tc.cover.applyCl" 40 $ "ps     =" <+> pretty (namedClausePats cl)
        reportSDoc "tc.cover.applyCl" 40 $ "mps    =" <+> pretty mps
        reportSDoc "tc.cover.applyCl" 40 $ "s      =" <+> pretty s
        reportSDoc "tc.cover.applyCl" 40 $ "new ps =" <+> pretty (s `applySubst` namedClausePats cl)
        return $
             Clause { clauseLHSRange  = clauseLHSRange cl
                    , clauseFullRange = clauseFullRange cl
                    , clauseTel       = tel
                    , namedClausePats = s `applySubst` namedClausePats cl
                    , clauseBody      = (s `applyPatSubst`) <$> clauseBody cl
                    , clauseType      = (s `applyPatSubst`) <$> clauseType cl
                    , clauseCatchall  = clauseCatchall cl
                    , clauseUnreachable = clauseUnreachable cl
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
          return $ CoverResult (SplittingDone (size tel)) Set.empty [] qs Set.empty
        Right (Covering n scs, x) -> do
          cs <- do
            let fallback = return cs
            caseMaybeM (getPrimitiveName' builtinHComp) fallback $ \ comp -> do
            let isComp = \case
                  SplitCon c -> comp == c
                  _ -> False
            caseMaybe (List.find (isComp . fst) scs) fallback $ \ (_, newSc) -> do
            snoc cs <$> createMissingHCompClause f n x sc newSc
          results <- mapM (cover f cs) (map snd scs)
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
          -- TODO Andrea: do something with etaRecordSplits and qsss?
          let trees' = zipWith (etaRecordSplits (unArg n) ps) scs trees
              tree   = SplitAt n trees'
          return $ CoverResult tree (Set.unions useds) (concat psss) (concat qsss) (Set.unions noex)

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
         caseMaybeM (splitResultPath f sc) fallback $ \ sc ->
               cover f cs . snd =<< fixTarget sc
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
            mapM (traverseF $ cover f cs <=< (snd <.> fixTarget)) scs
            -- OR:
            -- forM scs $ \ (proj, sc') -> (proj,) <$> do
            --   cover f cs =<< do
            --     snd <$> fixTarget sc'
          let trees = map coverSplitTree results
              useds = map coverUsedClauses results
              psss  = map coverMissingClauses results
              qsss  = map coverPatterns results
              noex  = map coverNoExactClauses results
              tree  = SplitAt n $ zip projs trees
          return $ CoverResult tree (Set.unions useds) (concat psss) (concat qsss) (Set.unions noex)

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
           LitP  _      -> gatherEtaSplits (-1) sc ps
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
      LitP  _      -> gatherEtaSplits n sc ps
      ProjP{}      -> gatherEtaSplits n sc ps

    addEtaSplits :: Int -> [NamedArg SplitPattern] -> SplitTree -> SplitTree
    addEtaSplits k []     t = t
    addEtaSplits k (p:ps) t = case namedArg p of
      VarP  _ _     -> addEtaSplits (k+1) ps t
      DotP  _ _     -> addEtaSplits (k+1) ps t
      ConP c cpi qs -> SplitAt (p $> k) [(SplitCon (conName c) , addEtaSplits k (qs ++ ps) t)]
      LitP  _       -> __IMPOSSIBLE__
      ProjP{}       -> __IMPOSSIBLE__
      DefP{}        -> __IMPOSSIBLE__ -- Andrea: maybe?
      IApplyP{}     -> addEtaSplits (k+1) ps t

    etaRecordSplits :: Int -> [NamedArg SplitPattern] -> (SplitTag,SplitClause)
                    -> SplitTree -> (SplitTag,SplitTree)
    etaRecordSplits n ps (q , sc) t =
      (q , addEtaSplits 0 (gatherEtaSplits n sc ps) t)




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
createMissingHCompClause f n x old_sc (SClause tel ps _sigma' cps (Just t)) = setCurrentRange f $ do
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
      rhoS = liftS (size hdelta) $ raiseS 3
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
            imin i j = pure tIMin <@> i <@> j
            trFillTel' a b c d = do
              m <- trFillTel <$> a <*> b <*> c <*> d
              x <- lift $ runExceptT m
              case x of
                Left bad_t -> cannotCreate "Cannot transport with type family:" bad_t
                Right args -> return args
          comp <- do
            let forward la bA r u = pure tTrans <#> (lam "i" $ \ i -> la <@> (i `imax` r))
                                              <@> (lam "i" $ \ i -> bA <@> (i `imax` r))
                                              <@> r
                                              <@> u
            return $ \ la bA phi u u0 ->
              pure tHComp <#> (la <@> pure io) <#> (bA <@> pure io) <#> phi
                        <@> (lam "i" $ \ i -> ilam "o" $ \ o ->
                                forward la bA i (u <@> i <..> o))
                        <@> forward la bA (pure iz) u0
          let
            hcomp la bA phi u u0 = pure tHComp <#> la <#> bA
                                               <#> phi
                                               <@> u
                                               <@> u0

            hfill la bA phi u u0 i = hcomp la bA
                                               (pure tIMax <@> phi <@> (pure tINeg <@> i))
                                               (lam "j" $ \ j -> pure tPOr <#> la <@> phi <@> (pure tINeg <@> i) <#> (ilam "o" $ \ _ -> bA)
                                                     <@> (ilam "o" $ \ o -> u <@> (pure tIMin <@> i <@> j) <..> o)
                                                     <@> (ilam "o" $ \ _ -> u0)
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
          old_t <- open $ raise (3+size delta) $ abstract hdelta (unArg old_t)
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
                    lift $ piApplyM hd $ [Arg (domInfo hdom) v] ++ args
          ty_level <- do
            t <- bind "i" ty
            s <- reduce $ getSort (absBody t)
            reportSDoc "tc.cover.hcomp" 20 $ text "ty_level, s = " <+> prettyTCM s
            case s of
              Type l -> open =<< (lam "i" $ \ _ -> pure $ Level l)
              _      -> cannotCreate "Cannot compose with type family:" =<< (liftTCM $ buildClosure t)

          let
            pOr_ty i phi psi u0 u1 = pure tPOr <#> (ty_level <@> i)
                                               <@> phi <@> psi
                                               <#> (ilam "o" $ \ _ -> unEl <$> ty i) <@> u0 <@> u1
          alpha <- do
            vars <- mapM (open . applySubst hcompS . fst) alphab
            return $ foldr imax (pure iz) $ map (\ v -> v `imax` ineg v) vars

          -- Γ,φ,u,u0,Δ(x = hcomp φ u u0) ⊢ b : (i : I) → [α] -> old_t[x = hfill φ u u0 i,δ_fill[i]]
          b <- do
             sides <- forM alphab $ \ (psi,(side0,side1)) -> do
                psi <- open $ hcompS `applySubst` psi

                [side0,side1] <- mapM (open . raise (3+size delta) . abstract hdelta) [side0,side1]
                return $ (ineg psi `imax` psi, \ i -> pOr_ty i (ineg psi) psi (ilam "o" $ \ _ -> apply_delta_fill i $ side0 <@> hfill lvl htype phi u u0 i)
                                                            (ilam "o" $ \ _ -> apply_delta_fill i $ side1 <@> hfill lvl htype phi u u0 i))
             let recurse []           i = __IMPOSSIBLE__
                 recurse [(psi,u)]    i = u i
                 recurse ((psi,u):xs) i = pOr_ty i psi (foldr imax (pure iz) (map fst xs)) (u i) (recurse xs i)
             return $ recurse sides

          ((,) <$> ty (pure io) <*>) $ do
            comp ty_level
               (lam "i" $ \ i -> unEl <$> ty i)
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
                    , clauseUnreachable = Just False  -- missing, thus, not unreachable
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
  (_x, rhs) <- case getHiding t of
    Instance{} -> addContext tel
                   $ locallyTC eCheckpoints (const cps)
                   $ checkpoint IdS    -- introduce a fresh checkpoint
                   $ newInstanceMeta "" (unArg t)
    Hidden     -> __IMPOSSIBLE__
    NotHidden  -> __IMPOSSIBLE__
  let cl = Clause { clauseLHSRange  = noRange
                  , clauseFullRange = noRange
                  , clauseTel       = tel
                  , namedClausePats = fromSplitPatterns ps
                  , clauseBody      = Just rhs
                  , clauseType      = Just t
                  , clauseCatchall  = False
                  , clauseUnreachable = Just False  -- missing, thus, not unreachable
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
    xs       = bs
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
        Datatype{dataPars = np, dataCons = cs, dataInduction = i}
          | i == CoInductive && ind /= CoInductive ->
              throw CoinductiveDatatype
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

-- | Update the target type, add more patterns to split clause
--   if target becomes a function type.
--   Returns the domains of the function type (if any).
fixTarget :: SplitClause -> TCM (Telescope, SplitClause)
fixTarget sc@SClause{ scTel = sctel, scPats = ps, scSubst = sigma, scCheckpoints = cps, scTarget = target } =
  caseMaybe target (return (empty, sc)) $ \ a -> do
    reportSDoc "tc.cover.target" 20 $ sep
      [ "split clause telescope: " <+> prettyTCM sctel
      , "old patterns          : " <+> do
          addContext sctel $ prettyTCMPatternList $ fromSplitPatterns ps
      ]
    reportSDoc "tc.cover.target" 60 $ sep
      [ "substitution          : " <+> prettyTCM sigma
      ]
    reportSDoc "tc.cover.target" 30 $ sep
      [ "target type before substitution (variables may be wrong): " <+> do
          addContext sctel $ prettyTCM a
      ]
    (TelV tel b) <- telViewUpTo (-1) $ applySplitPSubst sigma $ unArg a
    reportSDoc "tc.cover.target" 15 $ sep
      [ "target type telescope (after substitution): " <+> do
          addContext sctel $ prettyTCM tel
      , "target type core      (after substitution): " <+> do
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
          defp = DefP PatOSystem hCompName . map (setOrigin Inserted) $
                   map (fmap unnamed) [setHiding Hidden $ defaultArg $ applySubst rho1 $ DotP PatOSystem $ dlvl
                                      ,setHiding Hidden $ defaultArg $ applySubst rho1 $ DotP PatOSystem $ dterm]
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
  -> CoverM (Maybe SplitClause)   -- ^ New split clause if successful.
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

  -- All variables are flexible
  let flex = allFlexVars delta1Gamma

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

  r <- unifyIndices
         delta1Gamma
         flex
         (raise (size gamma) dtype)
         conIxs
         givenIxs

  case r of
    NoUnify {} -> debugNoUnify $> Nothing

    DontKnow errs -> do
      debugCantSplit
      throwError $ UnificationStuck (conName con) (delta1 `abstract` gamma) conIxs givenIxs errs
    Unifies (delta1',rho0,_) -> do
      debugSubst "rho0" rho0

      let rho0' = toSplitPSubst rho0

      -- We have Δ₁' ⊢ ρ₀ : Δ₁Γ, so split it into the part for Δ₁ and the part for Γ
      let (rho1,rho2) = splitS (size gamma) $ rho0'

      -- Andreas, 2015-05-01  I guess it is fine to use no @conPType@
      -- as the result of splitting is never used further down the pipeline.
      -- After splitting, Agda reloads the file.
      -- Andreas, 2017-09-03, issue #2729: remember that pattern was generated by case split.
      let cpi  = noConPatternInfo{ conPRecord = Just PatOSplit }
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

      let cps' = applySplitPSubst rho cps

      return $ Just $ SClause delta' ps' rho cps' Nothing -- target fixed later

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
          , "delta2 =" <+> do inTopContext $ addContext delta1 $ addContext gamma $ prettyTCM delta2
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

-- | Introduce trailing pattern variables via 'fixTarget'?
data FixTarget
  = YesFixTarget
  | NoFixTarget
  deriving (Eq, Show)

-- | Allow partial covering for split?
data AllowPartialCover
  = YesAllowPartialCover  -- To try to coverage-check incomplete splits.
  | NoAllowPartialCover   -- Default.
  deriving (Eq, Show)

-- | Entry point from @Interaction.MakeCase@.
splitClauseWithAbsurd :: SplitClause -> Nat -> TCM (Either SplitError (Either SplitClause Covering))
splitClauseWithAbsurd c x =
  split' CheckEmpty Inductive NoAllowPartialCover NoFixTarget c (BlockingVar x [] [] True)
  -- Andreas, 2016-05-03, issue 1950:
  -- Do not introduce trailing pattern vars after split,
  -- because this does not work for with-clauses.

-- | Entry point from @TypeChecking.Empty@ and @Interaction.BasicOps@.
--   @splitLast CoInductive@ is used in the @refine@ tactics.

splitLast :: Induction -> Telescope -> [NamedArg DeBruijnPattern] -> TCM (Either SplitError Covering)
splitLast ind tel ps = split ind NoAllowPartialCover sc (BlockingVar 0 [] [] True)
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
  fmap blendInAbsurdClause <$> split' NoCheckEmpty ind allowPartialCover YesFixTarget sc x
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
       -> FixTarget
          -- ^ If 'YesFixTarget', introduce new trailing variable patterns via
          --   'fixTarget'.
       -> SplitClause
       -> BlockingVar
       -> TCM (Either SplitError (Either SplitClause Covering))
split' checkEmpty ind allowPartialCover fixtarget
       sc@(SClause tel ps _ cps target) (BlockingVar x pcons' plits overlap) =
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
        hcompsc <- if isHIT && fixtarget == YesFixTarget
                   then computeHCompSplit delta1 n delta2 d pars ixs x tel ps cps
                   else return Nothing
        return $ (dr, catMaybes (mns ++ [hcompsc]))

      computeLitNeighborhoods = do
        typeOk <- liftTCM $ do
          t' <- litType $ headWithDefault {-'-} __IMPOSSIBLE__ plits
          liftTCM $ dontAssignMetas $ tryConversion $ equalType (unDom t) t'
        unless typeOk $ throwError . NotADatatype =<< do liftTCM $ buildClosure (unDom t)
        ns <- forM plits $ \lit -> do
          let delta2' = subst 0 (Lit $ vacuous lit) delta2
              delta'  = delta1 `abstract` delta2'
              rho     = liftS x $ consS (LitP lit) idS
              ps'     = applySubst rho ps
              cps'    = applySplitPSubst rho cps
          return (SplitLit lit , SClause delta' ps' rho cps' Nothing)
        ca <- do
          let delta' = tel -- telescope is unchanged for catchall branch
              varp   = VarP PatOSplit $ SplitPatVar
                         { splitPatVarName   = underscore
                         , splitPatVarIndex  = 0
                         , splitExcludedLits = plits
                         }
              rho    = liftS x $ consS varp $ raiseS 1
              ps'    = applySubst rho ps
          return (SplitCatchall , SClause delta' ps' rho cps Nothing)
        return (IsData , ns ++ [ ca ])

  (dr, ns) <- if null pcons' && not (null plits)
        then computeLitNeighborhoods
        else computeNeighborhoods

  ns <- case fixtarget of
    NoFixTarget  -> return ns
    YesFixTarget -> lift $ forM ns $ \(con,sc) ->
      (con,) . snd <$> fixTarget sc{ scTarget = target }

  -- Andreas, 2018-10-27, issue #3324; use isPropM.
  -- Need to reduce sort to decide on Prop.
  -- Cannot split if domain is a Prop but target is relevant.
  propArrowRel <- isPropM t `and2M`
    maybe (return True) (not <.> isPropM) target

  mHCompName <- getPrimitiveName' builtinHComp

  case ns of
    []  -> do
      let absurdp = VarP PatOAbsurd $ SplitPatVar underscore 0 []
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
    (_ : _ : _) | not (usableQuantity t) ->
      throwError . ErasedDatatype =<< do liftTCM $ inContextOfT $ buildClosure (unDom t)

    _ -> do

      -- Andreas, 2012-10-10 fail if precomputed constructor set does not cover
      -- all the data type constructors
      -- Andreas, 2017-10-08 ... unless partial covering is explicitly allowed.
      let ptags = map (SplitCon . conName) pcons' ++ map SplitLit plits
      -- clauses for hcomp will be automatically generated.
      let inferred_tags = maybe Set.empty (Set.singleton . SplitCon) mHCompName
      let all_tags = Set.fromList ptags `Set.union` inferred_tags

      when (allowPartialCover == NoAllowPartialCover && overlap == False) $
        for_ ns $ \(tag, sc) -> do
          when (not $ tag `Set.member` all_tags) $ do
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
    inContextOfT      = addContext tel . escapeContext (x + 1)
    inContextOfDelta2 = addContext tel . escapeContext x

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
        caseMaybeM (isPath (unArg t)) (return Nothing) $ \ _ -> do
               (TelV i b, boundary) <- telViewUpToPathBoundary' 1 (unArg t)
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
    , nest 2 $ "target =" <+> (addContext tel $ maybe empty prettyTCM target)
    ]
  -- if we want to split projections, but have no target type, we give up
  let failure = return . Left
  caseMaybe target (failure CosplitNoTarget) $ \ t -> do
    isR <- addContext tel $ isRecordType $ unArg t
    case isR of
      Just (_r, vs, Record{ recFields = fs }) -> do
        reportSDoc "tc.cover" 20 $ sep
          [ text $ "we are of record type _r = " ++ prettyShow _r
          , text   "applied to parameters vs = " <+> (addContext tel $ prettyTCM vs)
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
        reportSDoc "tc.cover" 20 $ sep
          [ text   "we are              self = " <+> (addContext tel $ prettyTCM $ unArg self)
          ]
        let n = defaultArg $ permRange $ fromMaybe __IMPOSSIBLE__ $ dbPatPerm $ fromSplitPatterns ps
            -- Andreas & James, 2013-11-19 includes the dot patterns!
            -- See test/succeed/CopatternsAndDotPatterns.agda for a case with dot patterns
            -- and copatterns which fails for @n = size tel@ with a broken case tree.

        -- Andreas, 2016-07-22 read the style of projections from the user's lips
        projOrigin <- ifM (optPostfixProjections <$> pragmaOptions) (return ProjPostfix) (return ProjPrefix)
        Right . Covering n <$> do
          forM fs $ \ proj -> do
            -- compute the new target
            dType <- defType <$> do getConstInfo $ unArg proj -- WRONG: typeOfConst $ unArg proj
            let -- type of projection instantiated at self
                target' = Just $ proj $> dType `piApply` pargs      -- Always visible (#2287)
                projArg = fmap (Named Nothing . ProjP projOrigin) $ setHiding NotHidden proj
                sc' = sc { scPats   = scPats sc ++ [projArg]
                         , scSubst  = idS
                         , scTarget = target'
                         }
            return (SplitCon (unArg proj), sc')
      _ -> addContext tel $ do
        buildClosure (unArg t) >>= failure . CosplitNoRecordType
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

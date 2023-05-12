{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NondecreasingIndentation #-}

-- | Checking local or global confluence of rewrite rules.
--
-- For checking LOCAL CONFLUENCE of a given rewrite rule @f ps ↦ v@,
-- we construct critical pairs involving this as the main rule by
-- searching for:
--
-- 1. *Different* rules @f ps' ↦ v'@ where @ps@ and @ps'@ can be
--    unified@.
--
-- 2. Subpatterns @g qs@ of @ps@ and rewrite rules @g qs' ↦ w@ where
--    @qs@ and @qs'@ can be unified.
--
-- Each of these leads to a *critical pair* @v₁ <-- u --> v₂@, which
-- should satisfy @v₁ = v₂@.
--
-- For checking GLOBAL CONFLUENCE, we check the following two
-- properties:
--
-- 1. For any two left-hand sides of the rewrite rules that overlap
--    (either at the root position or at a subterm), the most general
--    unifier of the two left-hand sides is again a left-hand side of
--    a rewrite rule. For example, if there are two rules @suc m + n =
--    suc (m + n)@ and @m + suc n = suc (m + n)@, then there should
--    also be a rule @suc m + suc n = suc (suc (m + n))@.
--
-- 2. Each rewrite rule should satisfy the *triangle property*: For
--    any rewrite rule @u = w@ and any single-step parallel unfolding
--    @u => v@, we should have another single-step parallel unfolding
--    @v => w@.


module Agda.TypeChecking.Rewriting.Confluence
  ( checkConfluenceOfRules
  , checkConfluenceOfClauses
  , sortRulesOfSymbol
  ) where

import Control.Applicative
import Control.Arrow ((***))
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader

import Data.Either
import Data.Function ( on )
import Data.Functor ( ($>) )
import qualified Data.HashMap.Strict as HMap
import Data.List ( elemIndex , tails )
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Interaction.Options ( ConfluenceCheck(..) )

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars

import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Conversion.Pure
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Free
import Agda.TypeChecking.Irrelevance ( isIrrelevantOrPropM )
import Agda.TypeChecking.Level
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Pretty.Warning
import Agda.TypeChecking.Pretty.Constraint
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Rewriting.Clause
import Agda.TypeChecking.Rewriting.NonLinMatch
import Agda.TypeChecking.Rewriting.NonLinPattern
import Agda.TypeChecking.Sort
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Warnings

import Agda.Utils.Applicative
import Agda.Utils.Functor
import Agda.Utils.Impossible
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.ListT
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null (unlessNullM)
import Agda.Utils.Permutation
import Agda.Utils.Singleton
import Agda.Utils.Size

-- ^ Check confluence of the clauses of the given function wrt rewrite rules of the
-- constructors they match against
checkConfluenceOfClauses :: ConfluenceCheck -> QName -> TCM ()
checkConfluenceOfClauses confChk f = do
  rews <- getClausesAsRewriteRules f
  let noMetasInPats rew
        | noMetas (rewPats rew) = return True
        | otherwise             = do
            genericWarning =<< do
              text "Confluence checking incomplete because the definition of" <+>
                prettyTCM f <+> text "contains unsolved metavariables."
            return False
  rews <- filterM noMetasInPats rews
  let matchables = map getMatchables rews
  reportSDoc "rewriting.confluence" 30 $
    "Function" <+> prettyTCM f <+> "has matchable symbols" <+> prettyList_ (map prettyTCM matchables)
  modifySignature $ setMatchableSymbols f $ concat matchables
  let hasRules g = not . null <$> getRewriteRulesFor g
  forM_ (zip rews matchables) $ \(rew,ms) ->
    unlessNullM (filterM hasRules ms) $ \_ -> do
      checkConfluenceOfRules confChk [rew]

-- ^ Check confluence of the given rewrite rules wrt all other rewrite
--   rules (also amongst themselves).
checkConfluenceOfRules :: ConfluenceCheck -> [RewriteRule] -> TCM ()
checkConfluenceOfRules confChk rews = inTopContext $ inAbstractMode $ do

  -- Global confluence: we need to check the triangle property for each rewrite
  -- rule of each head symbol as well as rules that match on them
  when (confChk == GlobalConfluenceCheck) $ do
    let getSymbols rew = let f = rewHead rew in
         (Set.insert f) . defMatchable <$> getConstInfo f
    allSymbols <- Set.toList . Set.unions <$> traverse getSymbols rews
    forM_ allSymbols $ \f -> do
      rewsf <- getAllRulesFor f
      forM_ rewsf $ \rew -> do
        reportSDoc "rewriting.confluence.triangle" 10 $
          "(re)checking triangle property for rule" <+> prettyTCM (rewName rew)
        checkTrianglePropertyForRule rew

  forM_ (tails rews) $ listCase (return ()) $ \rew rewsRest -> do

  reportSDoc "rewriting.confluence" 10 $
    "Checking confluence of rule" <+> prettyTCM (rewName rew)
  reportSDoc "rewriting.confluence" 30 $
    "Checking confluence of rule" <+> prettyTCM rew

  let f   = rewHead rew
      qs  = rewPats rew
      tel = rewContext rew
  def <- getConstInfo f
  (fa , hdf) <- addContext tel $ makeHead def (rewType rew)

  reportSDoc "rewriting.confluence" 30 $ addContext tel $
    "Head symbol" <+> prettyTCM (hdf []) <+> "of rewrite rule has type" <+> prettyTCM fa

  -- Step 1: check other rewrite rules that overlap at top position
  forMM_ (getAllRulesFor f) $ \ rew' -> do
    unless (any (sameRuleName rew') (rew:rewsRest) ||
            (rewFromClause rew && rewFromClause rew')) $
      checkConfluenceTop hdf rew rew'
  reportSDoc "rewriting.confluence" 30 $ "Finished step 1 of confluence check of rule" <+> prettyTCM (rewName rew)

  -- Step 2: check other rewrite rules that overlap with a subpattern
  -- of this rewrite rule
  es <- nlPatToTerm qs
  forMM_ (addContext tel $ allHolesList (fa, hdf) es) $ \ hole -> do
    let g   = ohHeadName hole
        hdg = ohHead hole
    reportSDoc "rewriting.confluence" 40 $
      "Found hole with head symbol" <+> prettyTCM g
    rews' <- getAllRulesFor g
    forM_ rews' $ \rew' -> do
      unless (any (sameRuleName rew') rewsRest) $
        checkConfluenceSub hdf hdg rew rew' hole
  reportSDoc "rewriting.confluence" 30 $ "Finished step 2 of confluence check of rule" <+> prettyTCM (rewName rew)

  -- Step 3: check other rewrite rules that have a subpattern which
  -- overlaps with this rewrite rule
  forM_ (defMatchable def) $ \ g -> do
    reportSDoc "rewriting.confluence" 40 $
      "Symbol" <+> prettyTCM g <+> "has rules that match on" <+> prettyTCM f
    forMM_ (getAllRulesFor g) $ \ rew' -> do
      unless (any (sameRuleName rew') rewsRest) $ do
        es' <- nlPatToTerm (rewPats rew')
        let tel' = rewContext rew'
        def' <- getConstInfo g
        (ga , hdg) <- addContext tel' $ makeHead def' (rewType rew')
        forMM_ (addContext tel' $ allHolesList (ga , hdg) es') $ \ hole -> do
          let f' = ohHeadName hole
          when (f == f') $ checkConfluenceSub hdg hdf rew' rew hole
  reportSDoc "rewriting.confluence" 30 $ "Finished step 3 of confluence check of rule" <+> prettyTCM (rewName rew)

  where

    -- Check confluence of two rewrite rules that have the same head symbol,
    -- e.g. @f ps --> a@ and @f ps' --> b@.
    checkConfluenceTop :: (Elims -> Term) -> RewriteRule -> RewriteRule -> TCM ()
    checkConfluenceTop hd rew1 rew2 =
      traceCall (CheckConfluence (rewName rew1) (rewName rew2)) $
      localTCStateSavingWarnings $ do

        sub1 <- makeMetaSubst $ rewContext rew1
        sub2 <- makeMetaSubst $ rewContext rew2

        let f    = rewHead rew1 -- == rewHead rew2
            a1   = applySubst sub1 $ rewType rew1
            a2   = applySubst sub2 $ rewType rew2

        es1 <- applySubst sub1 <$> nlPatToTerm (rewPats rew1)
        es2 <- applySubst sub2 <$> nlPatToTerm (rewPats rew2)

        reportSDoc "rewriting.confluence" 30 $ vcat
          [ "checkConfluenceTop" <+> prettyTCM (rewName rew1) <+> prettyTCM (rewName rew2)
          , "  f    = " <+> prettyTCM f
          , "  ctx1 = " <+> prettyTCM (rewContext rew1)
          , "  ctx2 = " <+> prettyTCM (rewContext rew2)
          , "  es1  = " <+> prettyTCM es1
          , "  es2  = " <+> prettyTCM es2
          ]

        -- Make sure we are comparing eliminations with the same arity
        -- (see #3810).
        let n = min (size es1) (size es2)
            (es1' , es1r) = splitAt n es1
            (es2' , es2r) = splitAt n es2
            esr           = es1r ++ es2r

            lhs1 = hd $ es1' ++ esr
            lhs2 = hd $ es2' ++ esr

            -- Use type of rewrite rule with the most eliminations
            a | null es1r = a2
              | otherwise = a1

        reportSDoc "rewriting.confluence" 20 $ sep
          [ "Considering potential critical pair at top-level: "
          , nest 2 $ prettyTCM $ lhs1, " =?= "
          , nest 2 $ prettyTCM $ lhs2 , " : " , nest 2 $ prettyTCM a
          ]

        maybeCriticalPair <- tryUnification lhs1 lhs2 $ do
          -- Unify the left-hand sides of both rewrite rules
          fa   <- defType <$> getConstInfo f
          fpol <- getPolarity' CmpEq f
          onlyReduceTypes $
            compareElims fpol [] fa (hd []) es1' es2'

          -- Get the rhs of both rewrite rules (after unification). In
          -- case of different arities, add additional arguments from
          -- one side to the other side.
          let rhs1 = applySubst sub1 (rewRHS rew1) `applyE` es2r
              rhs2 = applySubst sub2 (rewRHS rew2) `applyE` es1r

          return (rhs1 , rhs2)

        whenJust maybeCriticalPair $ uncurry (checkCriticalPair a hd (es1' ++ esr))

    -- Check confluence between two rules that overlap at a subpattern,
    -- e.g. @f ps[g qs] --> a@ and @g qs' --> b@.
    checkConfluenceSub :: (Elims -> Term) -> (Elims -> Term) -> RewriteRule -> RewriteRule -> OneHole Elims -> TCM ()
    checkConfluenceSub hdf hdg rew1 rew2 hole0 = do
      reportSDoc "rewriting.confluence" 100 $ "foo 2" <+> prettyTCM (rewName rew1) <+> prettyTCM (rewName rew2)
      traceCall (CheckConfluence (rewName rew1) (rewName rew2)) $ localTCStateSavingWarnings $ do

        reportSDoc "rewriting.confluence" 20 $
          "Checking confluence of rules" <+> prettyTCM (rewName rew1) <+>
          "and" <+> prettyTCM (rewName rew2) <+> "at subpattern position"

        sub1 <- makeMetaSubst $ rewContext rew1

        let bvTel0     = ohBoundVars hole0
            k          = size bvTel0
            b0         = applySubst (liftS k sub1) $ ohType hole0
            g          = ohHeadName hole0
            es0        = applySubst (liftS k sub1) $ ohElims hole0
            qs2        = rewPats rew2

        -- TODO: support IApply in forceEtaExpansion
        let isIApply IApply{} = True
            isIApply _        = False
        unless (any isIApply $ drop (size es0) qs2) $ do

        -- If the second rewrite rule has more eliminations than the
        -- subpattern of the first rule, the only chance of overlap is
        -- by eta-expanding the subpattern of the first rule.
        hole1 <- addContext bvTel0 $
          forceEtaExpansion b0 (hdg es0) $ drop (size es0) qs2

        verboseS "rewriting.confluence.eta" 30 $
          unless (size es0 == size qs2) $
          addContext bvTel0 $
          reportSDoc "rewriting.confluence.eta" 30 $ vcat
            [ "forceEtaExpansion result:"
            , nest 2 $ "bound vars: " <+> prettyTCM (ohBoundVars hole1)
            , nest 2 $ "hole contents: " <+> addContext (ohBoundVars hole1) (prettyTCM $ ohContents hole1)
            ]

        let hole      = hole1 `composeHole` hole0
            g         = ohHeadName hole -- == rewHead rew2
            es'       = ohElims hole
            bvTel     = ohBoundVars hole
            plug      = ohPlugHole hole

        sub2 <- addContext bvTel $ makeMetaSubst $ rewContext rew2

        let es1 = applySubst (liftS (size bvTel) sub1) es'
        es2 <- applySubst sub2 <$> nlPatToTerm (rewPats rew2)

        -- Make sure we are comparing eliminations with the same arity
        -- (see #3810). Because we forced eta-expansion of es1, we
        -- know that it is at least as long as es2.
        when (size es1 < size es2) __IMPOSSIBLE__
        let n = size es2
            (es1' , es1r) = splitAt n es1

        let lhs1 = applySubst sub1 $ hdf $ plug $ hdg es1
            lhs2 = applySubst sub1 $ hdf $ plug $ hdg $ es2 ++ es1r
            a    = applySubst sub1 $ rewType rew1

        reportSDoc "rewriting.confluence" 20 $ sep
          [ "Considering potential critical pair at subpattern: "
          , nest 2 $ prettyTCM $ lhs1 , " =?= "
          , nest 2 $ prettyTCM $ lhs2 , " : " , nest 2 $ prettyTCM a
          ]

        maybeCriticalPair <- tryUnification lhs1 lhs2 $ do
          -- Unify the subpattern of the first rewrite rule with the lhs
          -- of the second one
          ga   <- defType <$> getConstInfo g
          gpol <- getPolarity' CmpEq g
          onlyReduceTypes $ addContext bvTel $
            compareElims gpol [] ga (hdg []) es1' es2

          -- Right-hand side of first rewrite rule (after unification)
          let rhs1 = applySubst sub1 $ rewRHS rew1

          -- Left-hand side of first rewrite rule, with subpattern
          -- rewritten by the second rewrite rule
          let w = applySubst sub2 (rewRHS rew2) `applyE` es1r
          reportSDoc "rewriting.confluence" 30 $ sep
            [ "Plugging hole with w = "
            , nest 2 $ addContext bvTel $ prettyTCM w
            ]
          let rhs2 = applySubst sub1 $ hdf $ plug w

          return (rhs1 , rhs2)

        whenJust maybeCriticalPair $ uncurry (checkCriticalPair a hdf (applySubst sub1 $ plug $ hdg es1))

    checkCriticalPair
      :: Type     -- Type of the critical pair
      -> (Elims -> Term)  -- Head of lhs
      -> Elims            -- Eliminations of lhs
      -> Term     -- First reduct
      -> Term     -- Second reduct
      -> TCM ()
    checkCriticalPair a hd es rhs1 rhs2 = do

      (a,es,rhs1,rhs2) <- instantiateFull (a,es,rhs1,rhs2)

      let ms = Set.toList $ allMetas singleton $ (a,es,rhs1,rhs2)

      reportSDoc "rewriting.confluence" 30 $ sep
        [ "Abstracting over metas: "
        , prettyList_ (map (text . show) ms)
        ]
      (gamma , (a,es,rhs1,rhs2)) <- fromMaybe __IMPOSSIBLE__ <$>
        abstractOverMetas ms (a,es,rhs1,rhs2)

      addContext gamma $ reportSDoc "rewriting.confluence" 10 $ sep
        [ "Found critical pair: "
        , nest 2 $ prettyTCM (hd es)
        , " ---> " , nest 2 $ prettyTCM rhs1
        , " =?= " , nest 2 $ prettyTCM rhs2
        , " : " , nest 2 $ prettyTCM a ]
      reportSDoc "rewriting.confluence" 30 $ do
        gamma <- instantiateFull gamma
        sep [ "Context of critical pair: "
            , nest 2 $ prettyTCM gamma ]

      addContext gamma $ case confChk of

        -- Local confluence check: check that critical pair has a
        -- common reduct.
        LocalConfluenceCheck -> do
            dontAssignMetas $ noConstraints $ equalTerm a rhs1 rhs2
          `catchError` \case
            TypeError _ s err -> do
              prettyErr <- withTCState (const s) $ prettyTCM err
              warning $ RewriteNonConfluent (hd es) rhs1 rhs2 prettyErr
            err           -> throwError err

        -- Global confluence check: enforce that MGU is again the LHS
        -- of a rewrite rule (actual global confluence then follows
        -- from the triangle property which was checked before).
        GlobalConfluenceCheck -> do
          (f, t) <- fromMaybe __IMPOSSIBLE__ <$> getTypedHead (hd [])

          let checkEqualLHS :: RewriteRule -> TCM Bool
              checkEqualLHS (RewriteRule q delta _ ps _ _ _) = do
                onlyReduceTypes (nonLinMatch delta (t , hd) ps es) >>= \case
                  Left _    -> return False
                  Right sub -> do
                    let us = applySubst sub $ map var $ downFrom $ size delta
                        as = applySubst sub $ flattenTel delta
                    reportSDoc "rewriting.confluence.global" 35 $
                      prettyTCM (hd es) <+> "is an instance of the LHS of rule" <+> prettyTCM q <+> "with instantiation" <+> prettyList_ (map prettyTCM us)
                    ok <- allDistinctVars $ zip us as
                    when ok $ reportSDoc "rewriting.confluence.global" 30 $
                      "It is equal to the LHS of rewrite rule" <+> prettyTCM q
                    return ok
              allDistinctVars :: [(Term,Dom Type)] -> TCM Bool
              allDistinctVars us = do
                us' <- filterM (not <.> isIrrelevantOrPropM . snd) us
                mis <- traverse (\(u,a) -> isEtaVar u (unDom a)) $ us'
                case sequence mis of
                  Just is -> return $ fastDistinct is
                  Nothing -> return False

          rews <- getAllRulesFor f
          let sameRHS = onlyReduceTypes $ pureEqualTerm a rhs1 rhs2
          unlessM (sameRHS `or2M` anyM rews checkEqualLHS) $ addContext gamma $
            warning $ RewriteAmbiguousRules (hd es) rhs1 rhs2

    checkTrianglePropertyForRule :: RewriteRule -> TCM ()
    checkTrianglePropertyForRule (RewriteRule q gamma f ps rhs b c) = addContext gamma $ do
      u  <- nlPatToTerm $ PDef f ps
      -- First element in the list is the "best reduct" @ρ(u)@
      (rhou,vs) <- fromMaybe __IMPOSSIBLE__ . uncons <$> allParallelReductions u
      reportSDoc "rewriting.confluence" 40 $ ("rho(" <> prettyTCM u <> ") =") <+> prettyTCM rhou
      reportSDoc "rewriting.confluence" 40 $ ("S(" <> prettyTCM u <> ") =") <+> prettyList_ (map prettyTCM vs)
      -- If present, last element is always equal to u
      caseMaybe (initLast vs) (return ()) $ \(vs',u') -> do
        unless (u == u') __IMPOSSIBLE__
        forM_ vs' $ \v -> unlessM (checkParallelReductionStep b v rhou) $
          warning $ RewriteMissingRule u v rhou

    checkParallelReductionStep :: Type -> Term -> Term -> TCM Bool
    checkParallelReductionStep a u w = do
      reportSDoc "rewriting.confluence.global" 30 $ fsep
        [ "Global confluence: checking if" , prettyTCM u
        , "reduces to" , prettyTCM w , "in one parallel step." ]
      anyListT (parReduce u) $ \v -> do
        reportSDoc "rewriting.confluence.global" 30 $ fsep
          [ prettyTCM u , " reduces to " , prettyTCM v
          ]
        eq <- onlyReduceTypes $ pureEqualTerm a v w
        when eq $ reportSDoc "rewriting.confluence.global" 30 $ fsep
          [ "  which is equal to" , prettyTCM w
          ]
        return eq


sortRulesOfSymbol :: QName -> TCM ()
sortRulesOfSymbol f = do
    rules <- sortRules =<< getRewriteRulesFor f
    modifySignature $ over sigRewriteRules $ HMap.insert f rules
  where
    sortRules :: PureTCM m => [RewriteRule] -> m [RewriteRule]
    sortRules rs = do
      ordPairs <- deleteLoops . Set.fromList . map (rewName *** rewName) <$>
        filterM (uncurry $ flip moreGeneralLHS) [(r1,r2) | r1 <- rs, r2 <- rs]
      let perm = fromMaybe __IMPOSSIBLE__ $
                   topoSort (\r1 r2 -> (rewName r1,rewName r2) `Set.member` ordPairs) rs
      reportSDoc "rewriting.confluence.sort" 50 $ "sorted rules: " <+>
        prettyList_ (map (prettyTCM . rewName) $ permute perm rs)
      return $ permute perm rs

    moreGeneralLHS :: PureTCM m => RewriteRule -> RewriteRule -> m Bool
    moreGeneralLHS r1 r2
      | sameRuleName r1 r2       = return False
      | rewHead r1 /= rewHead r2 = return False
      | otherwise                = addContext (rewContext r2) $ do
          def <- getConstInfo $ rewHead r1
          (t, hd) <- makeHead def (rewType r2)
          (vs :: Elims) <- nlPatToTerm $ rewPats r2
          res <- isRight <$> onlyReduceTypes (nonLinMatch (rewContext r1) (t, hd) (rewPats r1) vs)
          when res $ reportSDoc "rewriting.confluence.sort" 55 $
            "the lhs of " <+> prettyTCM (rewName r1) <+>
            "is more general than the lhs of" <+> prettyTCM (rewName r2)
          return res

    deleteLoops :: Ord a => Set (a,a) -> Set (a,a)
    deleteLoops xs = Set.filter (\(x,y) -> not $ (y,x) `Set.member` xs) xs

makeHead :: PureTCM m => Definition -> Type -> m (Type , Elims -> Term)
makeHead def a = case theDef def of
  Constructor{ conSrcCon = ch } -> do
    ca <- snd . fromMaybe __IMPOSSIBLE__ <$> getFullyAppliedConType ch a
    return (ca , Con ch ConOSystem)
  -- For record projections @f : R Δ → A@, we rely on the invariant
  -- that any clause is fully general in the parameters, i.e. it
  -- is quantified over the parameter telescope @Δ@
  Function { funProjection = Right proj } -> do
    let f          = projOrig proj
        r          = unArg $ projFromType proj
    rtype <- defType <$> getConstInfo r
    TelV ptel _ <- telView rtype
    n <- getContextSize
    let pars :: Args
        pars = raise (n - size ptel) $ teleArgs ptel
    ftype <- defType def `piApplyM` pars
    return (ftype , Def f)
  _ -> return (defType def , Def $ defName def)

sameRuleName :: RewriteRule -> RewriteRule -> Bool
sameRuleName = (==) `on` rewName

-- | Get both clauses and rewrite rules for the given symbol
getAllRulesFor :: (HasConstInfo m, MonadFresh NameId m) => QName -> m [RewriteRule]
getAllRulesFor f = (++) <$> getRewriteRulesFor f <*> getClausesAsRewriteRules f

-- | Build a substitution that replaces all variables in the given
--   telescope by fresh metavariables.
makeMetaSubst :: (MonadMetaSolver m) => Telescope -> m Substitution
makeMetaSubst gamma = parallelS . reverse . map unArg <$> newTelMeta gamma

computingOverlap :: (MonadTCEnv m) => m a -> m a
computingOverlap = locallyTC eConflComputingOverlap $ const True

-- | Try to run the TCM action, return @Just x@ if it succeeds with
--   result @x@ or @Nothing@ if it throws a type error. Abort if there
--   are any constraints.
tryUnification :: Term -> Term -> TCM a -> TCM (Maybe a)
tryUnification lhs1 lhs2 f = computingOverlap (Just <$> f)
  `catchError` \case
    err@TypeError{} -> do
      reportSDoc "rewriting.confluence" 20 $ vcat
        [ "Unification failed with error: "
        , nest 2 $ prettyTCM err
        ]
      return Nothing
    err -> throwError err
  `ifNoConstraints` return $ \pid _ -> do
    cs <- getConstraintsForProblem pid
    prettyCs <- prettyInterestingConstraints cs
    warning $ RewriteMaybeNonConfluent lhs1 lhs2 prettyCs
    return Nothing


type MonadParallelReduce m =
  ( PureTCM m
  , MonadFresh NameId m
  )

-- | List all possible single-step parallel reductions of the given term.
allParallelReductions :: (MonadParallelReduce m, ParallelReduce a) => a -> m [a]
allParallelReductions = sequenceListT . parReduce

-- | Single-step parallel reduction of a given term.
--   The monad 'm' can be instantiated in multiple ways:
--   * Use 'MaybeT TCM' to get the "optimal reduct" obtained by
--     applying rewrite rules eagerly.
--   * Use 'ListT TCM' to obtain all possible one-step parallel
--     reductions.
class ParallelReduce a where
  parReduce :: (MonadParallelReduce m, MonadPlus m) => a -> m a

  default parReduce
    :: ( MonadParallelReduce m, MonadPlus m
       , Traversable f, a ~ f b, ParallelReduce b)
    => a -> m a
  parReduce = traverse parReduce

-- | Compute possible one-step reductions by applying a rewrite rule
--   at the top-level and reducing all subterms in the position of a
--   variable of the rewrite rule in parallel.
topLevelReductions :: (MonadParallelReduce m, MonadPlus m) => (Elims -> Term) -> Elims -> m Term
topLevelReductions hd es = do
  reportSDoc "rewriting.parreduce" 30 $ "topLevelReductions" <+> prettyTCM (hd es)
  -- Get type of head symbol
  (f , t) <- fromMaybe __IMPOSSIBLE__ <$> getTypedHead (hd [])
  reportSDoc "rewriting.parreduce" 60 $ "topLevelReductions: head symbol" <+> prettyTCM (hd []) <+> ":" <+> prettyTCM t
  RewriteRule q gamma _ ps rhs b c <- scatterMP (getAllRulesFor f)
  reportSDoc "rewriting.parreduce" 60 $ "topLevelReductions: trying rule" <+> prettyTCM q
  -- Don't reduce if underapplied
  guard $ length es >= length ps
  let (es0 , es1) = splitAt (length ps) es
  onlyReduceTypes (nonLinMatch gamma (t,hd) ps es0) >>= \case
    -- Matching failed: no reduction
    Left block -> empty
    -- Matching succeeded
    Right sub -> do
      let vs = map (lookupS sub) $ [0..(size gamma-1)]
      sub' <- parallelS <$> parReduce vs
      es1' <- parReduce es1
      let w = (applySubst sub' rhs) `applyE` es1'
      reportSDoc "rewriting.parreduce" 50 $ "topLevelReductions: rewrote" <+> prettyTCM (hd es) <+> "to" <+> prettyTCM w
      return w

instance ParallelReduce Term where
  parReduce = \case
    -- Interesting cases
    (Def f es) -> (topLevelReductions (Def f) es) <|> (Def f <$> parReduce es)
    (Con c ci es) -> (topLevelReductions (Con c ci) es) <|> (Con c ci <$> parReduce es)

    -- Congruence cases
    Lam i u  -> Lam i <$> parReduce u
    Var x es -> Var x <$> parReduce es
    Pi a b   -> Pi    <$> parReduce a <*> parReduce b
    Sort s   -> Sort  <$> parReduce s

    -- Base cases
    u@Lit{}      -> return u
    u@Level{}    -> return u -- TODO: is this fine?
    u@DontCare{} -> return u
    u@Dummy{}    -> return u -- not __IMPOSSIBLE__ because of presence of Dummy
                             -- parameters for rewrite rules on constructors.

    -- Impossible cases
    MetaV{}    -> __IMPOSSIBLE__

instance ParallelReduce Sort where
  parReduce = pure -- TODO: is this fine?

instance ParallelReduce a => ParallelReduce (Arg a) where
instance ParallelReduce a => ParallelReduce (Dom a) where
instance ParallelReduce a => ParallelReduce (Type' a) where
instance ParallelReduce a => ParallelReduce [a] where

instance ParallelReduce a => ParallelReduce (Elim' a) where
  parReduce (Apply u)  = Apply <$> parReduce u
  parReduce e@Proj{}   = pure e
  parReduce e@IApply{} = pure e -- TODO

instance (Free a, Subst a, ParallelReduce a) => ParallelReduce (Abs a) where
  parReduce = mapAbstraction __DUMMY_DOM__ parReduce


-- | Given metavariables ms and some x, construct a telescope Γ and
--   replace all occurrences of the given metavariables in @x@ by
--   normal variables from Γ. Returns @Nothing@ if metas have cyclic
--   dependencies.
abstractOverMetas :: (MetasToVars a) => [MetaId] -> a -> TCM (Maybe (Telescope, a))
abstractOverMetas ms x = do

  -- Sort metas in dependency order
  forMM (dependencySortMetas ms) $ \ms' -> do

    -- Get types and suggested names of metas
    as <- forM ms' getMetaType
    ns <- forM ms' getMetaNameSuggestion

    -- Construct telescope (still containing the metas)
    let n     = size ms'
        gamma = unflattenTel' n ns $ map defaultDom as

    -- Replace metas by variables
    let metaIndex x = (n-1-) <$> elemIndex x ms'
    runReaderT (metasToVars (gamma, x)) metaIndex

-- ^ A @OneHole p@ is a @p@ with a subpattern @f ps@ singled out.
data OneHole a = OneHole
  { ohBoundVars :: Telescope     -- Telescope of bound variables at the hole
  , ohType      :: Type          -- Type of the term in the hole
  , ohPlugHole  :: Term -> a     -- Plug the hole with some term
  , ohHead      :: Elims -> Term -- The head symbol of the term in the hole
  , ohElims     :: Elims         -- The eliminations of the term in the hole
  } deriving (Functor)

ohHeadName :: OneHole a -> QName
ohHeadName oh = case ohHead oh [] of
  Def f _   -> f
  Con c _ _ -> conName c
  _         -> __IMPOSSIBLE__

ohContents :: OneHole a -> Term
ohContents oh = ohHead oh $ ohElims oh

-- | The trivial hole
idHole :: Type -> Term -> OneHole Term
idHole a = \case
  Def f es    -> OneHole EmptyTel a id (Def f) es
  Con c ci es -> OneHole EmptyTel a id (Con c ci) es
  _           -> __IMPOSSIBLE__

-- | Plug a hole with another hole
composeHole :: OneHole Term -> OneHole a -> OneHole a
composeHole inner outer = OneHole
  { ohBoundVars = ohBoundVars outer `abstract` ohBoundVars inner
  , ohType      = ohType inner
  , ohPlugHole  = ohPlugHole outer . ohPlugHole inner
  , ohHead      = ohHead inner
  , ohElims     = ohElims inner
  }

ohAddBV :: ArgName -> Dom Type -> OneHole a -> OneHole a
ohAddBV x a oh = oh { ohBoundVars = ExtendTel a $ Abs x $ ohBoundVars oh }

-- ^ Given a @p : a@, @allHoles p@ lists all the possible
--   decompositions @p = p'[(f ps)/x]@.
class (TermSubst p, Free p) => AllHoles p where
  allHoles :: (Alternative m, PureTCM m) => TypeOf p -> p -> m (OneHole p)

allHoles_
  :: ( Alternative m , PureTCM m , AllHoles p , TypeOf p ~ () )
  => p -> m (OneHole p)
allHoles_ = allHoles ()

allHolesList
  :: ( PureTCM m , AllHoles p)
  => TypeOf p -> p -> m [OneHole p]
allHolesList a = sequenceListT . allHoles a

-- | Given a term @v : a@ and eliminations @es@, force eta-expansion
--   of @v@ to match the structure (Apply/Proj) of the eliminations.
--
--   Examples:
--
--   1. @v : _A@ and @es = [$ w]@: this will instantiate
--      @_A := (x : _A1) → _A2@ and return the @OneHole Term@
--      @λ x → [v x]@.
--
--   2. @v : _A@ and @es = [.fst]@: this will instantiate
--      @_A := _A1 × _A2@ and return the @OneHole Term@
--      @([v .fst]) , (v .snd)@.
forceEtaExpansion :: Type -> Term -> [Elim' a] -> TCM (OneHole Term)
forceEtaExpansion a v [] = return $ idHole a v
forceEtaExpansion a v (e:es) = case e of

  Apply (Arg i w) -> do

    -- Force a to be a pi type
    reportSDoc "rewriting.confluence.eta" 40 $ fsep
      [ "Forcing" , prettyTCM v , ":" , prettyTCM a , "to take one more argument" ]
    dom <- defaultArgDom i <$> newTypeMeta_
    cod <- addContext dom $ newTypeMeta_
    equalType a $ mkPi (("x",) <$> dom) cod

    -- Construct body of eta-expansion
    let body = raise 1 v `apply` [Arg i $ var 0]

    -- Continue with remaining eliminations
    addContext dom $ ohAddBV "x" dom . fmap (Lam i . mkAbs "x") <$>
      forceEtaExpansion cod body es

  Proj o f -> do

    -- Force a to be the right record type for projection by f
    reportSDoc "rewriting.confluence.eta" 40 $ fsep
      [ "Forcing" , prettyTCM v , ":" , prettyTCM a , "to be projectible by" , prettyTCM f ]
    r <- fromMaybe __IMPOSSIBLE__ <$> getRecordOfField f
    rdef <- getConstInfo r
    let ra = defType rdef
    pars <- newArgsMeta ra
    s <- ra `piApplyM` pars >>= \s -> ifIsSort s return __IMPOSSIBLE__
    equalType a $ El s (Def r $ map Apply pars)

    -- Eta-expand v at record type r, and get field corresponding to f
    (_ , c , ci , fields) <- etaExpandRecord_ r pars (theDef rdef) v
    let fs        = map argFromDom $ recFields $ theDef rdef
        i         = fromMaybe __IMPOSSIBLE__ $ elemIndex f $ map unArg fs
        fContent  = unArg $ fromMaybe __IMPOSSIBLE__ $ fields !!! i
        fUpdate w = Con c ci $ map Apply $ updateAt i (w <$) fields

    -- Get type of field corresponding to f
    ~(Just (El _ (Pi b c))) <- getDefType f =<< reduce a
    let fa = c `absApp` v

    -- Continue with remaining eliminations
    fmap fUpdate <$> forceEtaExpansion fa fContent es

  IApply{} -> __IMPOSSIBLE__ -- Not yet implemented

-- ^ Instances for @AllHoles@

instance AllHoles p => AllHoles (Arg p) where
  allHoles a x = fmap (x $>) <$> allHoles (unDom a) (unArg x)

instance AllHoles p => AllHoles (Dom p) where
  allHoles a x = fmap (x $>) <$> allHoles a (unDom x)

instance AllHoles (Abs Term) where
  allHoles (dom , a) x = addContext (absName x , dom) $
    ohAddBV (absName a) dom . fmap (mkAbs $ absName x) <$>
      allHoles (absBody a) (absBody x)

instance AllHoles (Abs Type) where
  allHoles dom a = addContext (absName a , dom) $
    ohAddBV (absName a) dom . fmap (mkAbs $ absName a) <$>
      allHoles_ (absBody a)

instance AllHoles Elims where
  allHoles (a,hd) [] = empty
  allHoles (a,hd) (e:es) = do
    reportSDoc "rewriting.confluence.hole" 65 $ fsep
      [ "Head symbol" , prettyTCM (hd []) , ":" , prettyTCM a
      , "is eliminated by" , prettyTCM e
      ]
    case e of
      Apply x -> do
        ~(Pi b c) <- unEl <$> reduce a
        let a'  = c `absApp` unArg x
            hd' = hd . (e:)
        (fmap ((:es) . Apply) <$> allHoles b x)
         <|> (fmap (e:) <$> allHoles (a' , hd') es)
      Proj o f -> do
        ~(Just (El _ (Pi b c))) <- getDefType f =<< reduce a
        let a' = c `absApp` hd []
        hd' <- applyE <$> applyDef o f (argFromDom b $> hd [])
        fmap (e:) <$> allHoles (a' , hd') es
      IApply x y u -> empty -- TODO: support --confluence-check + --cubical

instance AllHoles Type where
  allHoles _ (El s a) = workOnTypes $
    fmap (El s) <$> allHoles (sort s) a

instance AllHoles Term where
  allHoles a u = do
    reportSDoc "rewriting.confluence.hole" 60 $ fsep
      [ "Getting holes of term" , prettyTCM u , ":" , prettyTCM a ]
    case u of
      Var i es       -> do
        ai <- typeOfBV i
        fmap (Var i) <$> allHoles (ai , Var i) es
      Lam i u        -> do
        ~(Pi b c) <- unEl <$> reduce a
        fmap (Lam i) <$> allHoles (b,c) u
      Lit l          -> empty
      v@(Def f es)   -> do
        fa <- defType <$> getConstInfo f
        pure (idHole a v)
         <|> (fmap (Def f) <$> allHoles (fa , Def f) es)
      v@(Con c ci es) -> do
        ca <- snd . fromMaybe __IMPOSSIBLE__ <$> do
          getFullyAppliedConType c =<< reduce a
        pure (idHole a v)
         <|> (fmap (Con c ci) <$> allHoles (ca , Con c ci) es)
      Pi a b         ->
        (fmap (\a -> Pi a b) <$> allHoles_ a) <|>
        (fmap (\b -> Pi a b) <$> allHoles a b)
      Sort s         -> fmap Sort <$> allHoles_ s
      Level l        -> fmap Level <$> allHoles_ l
      MetaV{}        -> __IMPOSSIBLE__
      DontCare{}     -> empty
      Dummy{}        -> empty

instance AllHoles Sort where
  allHoles _ = \case
    Univ u l     -> fmap (Univ u) <$> allHoles_ l
    Inf f n      -> empty
    SizeUniv     -> empty
    LockUniv     -> empty
    LevelUniv    -> empty
    IntervalUniv -> empty
    PiSort{}     -> __IMPOSSIBLE__
    FunSort{}    -> __IMPOSSIBLE__
    UnivSort{}   -> __IMPOSSIBLE__
    MetaS{}      -> __IMPOSSIBLE__
    DefS f es    -> do
      fa <- defType <$> getConstInfo f
      fmap (DefS f) <$> allHoles (fa , Def f) es
    DummyS{}     -> empty

instance AllHoles Level where
  allHoles _ (Max n ls) = fmap (Max n) <$> allHoles_ ls

instance AllHoles [PlusLevel] where
  allHoles _ []     = empty
  allHoles _ (l:ls) =
    (fmap (:ls) <$> allHoles_ l)
    <|> (fmap (l:) <$> allHoles_ ls)

instance AllHoles PlusLevel where
  allHoles _ (Plus n l) = do
    la <- levelType'
    fmap (Plus n) <$> allHoles la l


-- | Convert metavariables to normal variables. Warning: doesn't
--   convert sort metas.
class MetasToVars a where
  metasToVars
    :: (MonadReader (MetaId -> Maybe Nat) m , HasBuiltins m)
    => a -> m a

  default metasToVars
    :: ( MetasToVars a', Traversable f, a ~ f a'
       , MonadReader (MetaId -> Maybe Nat) m , HasBuiltins m)
    => a -> m a
  metasToVars = traverse metasToVars

instance MetasToVars a => MetasToVars [a] where
instance MetasToVars a => MetasToVars (Arg a) where
instance MetasToVars a => MetasToVars (Dom a) where
instance MetasToVars a => MetasToVars (Elim' a) where

instance MetasToVars a => MetasToVars (Abs a) where
  metasToVars (Abs   i x) = Abs i   <$> local (fmap succ .) (metasToVars x)
  metasToVars (NoAbs i x) = NoAbs i <$> metasToVars x

instance MetasToVars Term where
  metasToVars = \case
    Var i es   -> Var i    <$> metasToVars es
    Lam i u    -> Lam i    <$> metasToVars u
    Lit l      -> pure (Lit l)
    Def f es   -> Def f    <$> metasToVars es
    Con c i es -> Con c i  <$> metasToVars es
    Pi a b     -> Pi       <$> metasToVars a <*> metasToVars b
    Sort s     -> Sort     <$> metasToVars s
    Level l    -> Level    <$> metasToVars l
    MetaV x es -> asks ($ x) >>= \case
      Just i   -> Var i    <$> metasToVars es
      Nothing  -> MetaV x  <$> metasToVars es
    DontCare u -> DontCare <$> metasToVars u
    Dummy s es -> Dummy s  <$> metasToVars es

instance MetasToVars Type where
  metasToVars (El s t) = El <$> metasToVars s <*> metasToVars t

instance MetasToVars Sort where
  metasToVars = \case
    Univ u l   -> Univ u <$> metasToVars l
    Inf f n    -> pure $ Inf f n
    SizeUniv   -> pure SizeUniv
    LockUniv   -> pure LockUniv
    LevelUniv  -> pure LevelUniv
    IntervalUniv -> pure IntervalUniv
    PiSort s t u -> PiSort   <$> metasToVars s <*> metasToVars t <*> metasToVars u
    FunSort s t -> FunSort <$> metasToVars s <*> metasToVars t
    UnivSort s -> UnivSort <$> metasToVars s
    MetaS x es -> MetaS x  <$> metasToVars es
    DefS f es  -> DefS f   <$> metasToVars es
    DummyS s   -> pure $ DummyS s

instance MetasToVars Level where
  metasToVars (Max n ls) = Max n <$> metasToVars ls

instance MetasToVars PlusLevel where
  metasToVars (Plus n x) = Plus n <$> metasToVars x

instance MetasToVars a => MetasToVars (Tele a) where
  metasToVars EmptyTel = pure EmptyTel
  metasToVars (ExtendTel a tel) = ExtendTel <$> metasToVars a <*> metasToVars tel

instance (MetasToVars a, MetasToVars b) => MetasToVars (a,b) where
  metasToVars (x,y) = (,) <$> metasToVars x <*> metasToVars y

instance (MetasToVars a, MetasToVars b, MetasToVars c) => MetasToVars (a,b,c) where
  metasToVars (x,y,z) = (,,) <$> metasToVars x <*> metasToVars y <*> metasToVars z

instance (MetasToVars a, MetasToVars b, MetasToVars c, MetasToVars d) => MetasToVars (a,b,c,d) where
  metasToVars (x,y,z,w) = (,,,) <$> metasToVars x <*> metasToVars y <*> metasToVars z <*> metasToVars w

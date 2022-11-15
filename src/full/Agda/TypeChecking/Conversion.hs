{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}

#if __GLASGOW_HASKELL__ >= 810
{-# OPTIONS_GHC -fmax-pmcheck-models=390 #-} -- Andreas, 2023-05-12, limit determined by binary search
#endif

module Agda.TypeChecking.Conversion where

import Control.Arrow (second)
import Control.Monad.Except ( MonadError(..) )

import Data.Function (on)
import Data.Semigroup ((<>))
import Data.IntMap (IntMap)

import qualified Data.List   as List
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Set    as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars
import Agda.Syntax.Translation.InternalToAbstract (reify)

import Agda.TypeChecking.Monad
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.MetaVars.Occurs (killArgs,PruneResult(..),rigidVarsNotContainedIn)
import Agda.TypeChecking.Names
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import qualified Agda.TypeChecking.SyntacticEquality as SynEq
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion.Pure (pureCompareAs, runPureConversion)
import Agda.TypeChecking.Forcing (isForced, nextIsForced)
import Agda.TypeChecking.Free
import Agda.TypeChecking.Datatypes (getConType, getFullyAppliedConType)
import Agda.TypeChecking.Records
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Injectivity
import Agda.TypeChecking.Polarity
import Agda.TypeChecking.SizedTypes
import Agda.TypeChecking.Level
import Agda.TypeChecking.Implicit (implicitArgs)
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.ProjectionLike
import Agda.TypeChecking.Warnings (MonadWarning)
import Agda.Interaction.Options

import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List1 (List1, pattern (:|))
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Monad
import Agda.Utils.Maybe
import Agda.Utils.Permutation
import Agda.Syntax.Common.Pretty (prettyShow)
import qualified Agda.Utils.ProfileOptions as Profile
import Agda.Utils.BoolSet (BoolSet)
import qualified Agda.Utils.BoolSet as BoolSet
import Agda.Utils.Size
import Agda.Utils.Tuple
import Agda.Utils.Unsafe ( unsafeComparePointers )

import Agda.Utils.Impossible

type MonadConversion m =
  ( PureTCM m
  , MonadConstraint m
  , MonadMetaSolver m
  , MonadError TCErr m
  , MonadWarning m
  , MonadStatistics m
  , MonadFresh ProblemId m
  , MonadFresh Int m
  )

-- | Try whether a computation runs without errors or new constraints
--   (may create new metas, though).
--   Restores state upon failure.
tryConversion
  :: (MonadConstraint m, MonadWarning m, MonadError TCErr m, MonadFresh ProblemId m)
  => m () -> m Bool
tryConversion = isJust <.> tryConversion'

-- | Try whether a computation runs without errors or new constraints
--   (may create new metas, though).
--   Return 'Just' the result upon success.
--   Return 'Nothing' and restore state upon failure.
tryConversion'
  :: (MonadConstraint m, MonadWarning m, MonadError TCErr m, MonadFresh ProblemId m)
  => m a -> m (Maybe a)
tryConversion' m = tryMaybe $ noConstraints m

-- | Check if to lists of arguments are the same (and all variables).
--   Precondition: the lists have the same length.
sameVars :: Elims -> Elims -> Bool
sameVars xs ys = and $ zipWith same xs ys
    where
        same (Apply (Arg _ (Var n []))) (Apply (Arg _ (Var m []))) = n == m
        same _ _ = False

-- | @intersectVars us vs@ checks whether all relevant elements in @us@ and @vs@
--   are variables, and if yes, returns a prune list which says @True@ for
--   arguments which are different and can be pruned.
intersectVars :: Elims -> Elims -> Maybe [Bool]
intersectVars = zipWithM areVars where
    -- ignore irrelevant args
    areVars (Apply u) v | isIrrelevant u = Just False -- do not prune
    areVars (Apply (Arg _ (Var n []))) (Apply (Arg _ (Var m []))) = Just $ n /= m -- prune different vars
    areVars _ _                                   = Nothing

-- | @guardPointerEquality x y s m@ behaves as @m@ if @x@ and @y@ are equal as pointers,
-- or does nothing otherwise.
-- Use with care, see the documentation for 'unsafeComparePointers'
guardPointerEquality :: MonadConversion m => a -> a -> String -> m () -> m ()
guardPointerEquality u v profileSection action =
  if unsafeComparePointers u v
  then whenProfile Profile.Conversion $ tick profileSection
  else action

{-# SPECIALIZE equalTerm :: Type -> Term -> Term -> TCM () #-}
equalTerm :: MonadConversion m => Type -> Term -> Term -> m ()
equalTerm = compareTerm CmpEq

{-# SPECIALIZE equalAtom :: CompareAs -> Term -> Term -> TCM () #-}
equalAtom :: MonadConversion m => CompareAs -> Term -> Term -> m ()
equalAtom = compareAtom CmpEq

{-# SPECIALIZE equalType :: Type -> Type -> TCM () #-}
equalType :: MonadConversion m => Type -> Type -> m ()
equalType = compareType CmpEq

{- Comparing in irrelevant context always succeeds.

   However, we might want to dig for solutions of irrelevant metas.

   To this end, we can just ignore errors during conversion checking.
 -}

-- convError ::  MonadTCM tcm => TypeError -> tcm a
-- | Ignore errors in irrelevant context.
convError :: TypeError -> TCM ()
convError err =
  ifM (isIrrelevant <$> viewTC eRelevance)
    (return ())
    (typeError err)


-- | Type directed equality on values.
--
compareTerm :: forall m. MonadConversion m => Comparison -> Type -> Term -> Term -> m ()
compareTerm cmp a u v = compareAs cmp (AsTermsOf a) u v


{-# SPECIALIZE compareAs :: Comparison -> CompareAs -> Term -> Term -> TCM ()  #-}
-- | Type directed equality on terms or types.
compareAs :: forall m. MonadConversion m => Comparison -> CompareAs -> Term -> Term -> m ()
  -- If one term is a meta, try to instantiate right away. This avoids unnecessary unfolding.
  -- Andreas, 2012-02-14: This is UNSOUND for subtyping!
compareAs cmp a u v = do
  reportSDoc "tc.conv.term" 20 $ sep $
    [ "compareTerm"
    , nest 2 $ prettyTCM u <+> prettyTCM cmp <+> prettyTCM v
    , nest 2 $ prettyTCM a
    ]
  whenProfile Profile.Conversion $ tick "compare"

  -- OLD CODE, traverses the *full* terms u v at each step, even if they
  -- are different somewhere.  Leads to infeasibility in issue 854.
  -- (u, v) <- instantiateFull (u, v)
  -- let equal = u == v

  -- Check syntactic equality. This actually saves us quite a bit of work.
  guardPointerEquality u v "pointer equality: terms" $ SynEq.checkSyntacticEquality u v
    (\_ _ -> whenProfile Profile.Conversion $ tick "compare equal") $
    \u v -> do
      reportSDoc "tc.conv.term" 15 $ sep $
        [ "compareTerm (not syntactically equal)"
        , nest 2 $ prettyTCM u <+> prettyTCM cmp <+> prettyTCM v
        , nest 2 $ prettyTCM a
        ]
      -- If we are at type Size, we cannot short-cut comparison
      -- against metas by assignment.
      -- Andreas, 2014-04-12: this looks incomplete.
      -- It seems to assume we are never comparing
      -- at function types into Size.
      let fallback = compareAs' cmp a u v
          unlessSubtyping :: m () -> m ()
          unlessSubtyping cont =
              if cmp == CmpEq then cont else do
                -- Andreas, 2014-04-12 do not short cut if type is blocked.
                ifBlocked a (\ _ _ -> fallback) {-else-} $ \ _ a -> do
                  -- do not short circuit size comparison!
                  caseMaybeM (isSizeType a) cont (\ _ -> fallback)

          dir = fromCmp cmp
          rid = flipCmp dir     -- The reverse direction.  Bad name, I know.
      case (u, v) of
        (MetaV x us, MetaV y vs)
          | x /= y    -> unlessSubtyping $ solve1 `orelse` solve2 `orelse` fallback
          | otherwise -> fallback
          where
            (solve1, solve2) | x > y     = (assign dir x us v, assign rid y vs u)
                             | otherwise = (assign rid y vs u, assign dir x us v)
        (MetaV x us, _) -> unlessSubtyping $ assign dir x us v `orelse` fallback
        (_, MetaV y vs) -> unlessSubtyping $ assign rid y vs u `orelse` fallback
        (Def f es, Def f' es') | f == f' -> do
          def <- getConstInfo f
          opts <- pragmaOptions
          let shortcut = case theDef def of
                _ | optFirstOrder opts                       -> True
                d@Function{}
                  | not $ optRequireUniqueMetaSolutions opts -> d ^. funFirstOrder
                _                                            -> False
          if not shortcut then fallback else unlessSubtyping $ do
          -- We do not shortcut projection-likes,
          -- Andreas, 2022-03-07, issue #5809:
          -- but irrelevant projections since they are applied to their parameters.
          -- Amy, 2023-01-04, issue #6415: and not
          -- prim^unglue/prim^unglueU either! removing the unglue from a
          -- transport/hcomp may cause an infinite loop.
          cubicalProjs <- traverse getName' [builtin_unglue, builtin_unglueU]
          let
            notFirstOrder = isJust (isRelevantProjection_ def)
                         || (Just f) `elem` cubicalProjs
          if notFirstOrder then fallback else do
          pol <- getPolarity' cmp f
          whenProfile Profile.Conversion $ tick "compare first-order shortcut"
          compareElims pol [] (defType def) (Def f []) es es' `orelse` fallback
        _               -> fallback
  where
    assign :: CompareDirection -> MetaId -> Elims -> Term -> m ()
    assign dir x es v = do
      -- Andreas, 2013-10-19 can only solve if no projections
      reportSDoc "tc.conv.term.shortcut" 20 $ sep
        [ "attempting shortcut"
        , nest 2 $ prettyTCM (MetaV x es) <+> ":=" <+> prettyTCM v
        ]
      whenM (isInstantiatedMeta x) (patternViolation alwaysUnblock) -- Already instantiated, retry right away
      whenProfile Profile.Conversion $ tick "compare meta shortcut"
      assignE dir x es v a $ compareAsDir dir a
      reportSDoc "tc.conv.term.shortcut" 50 $
        "shortcut successful" $$ nest 2 ("result:" <+> (pretty =<< instantiate (MetaV x es)))
      whenProfile Profile.Conversion $ tick "compare meta shortcut successful"
    -- Should be ok with catchError_ but catchError is much safer since we don't
    -- rethrow errors.
    orelse :: m () -> m () -> m ()
    orelse m h = catchError m (\_ -> h)

-- | Try to assign meta.  If meta is projected, try to eta-expand
--   and run conversion check again.
assignE :: (MonadConversion m)
        => CompareDirection -> MetaId -> Elims -> Term -> CompareAs -> (Term -> Term -> m ()) -> m ()
assignE dir x es v a comp = do
  whenProfile Profile.Conversion $ tick "compare meta"
  case allApplyElims es of
    Just vs -> assignV dir x vs v a
    Nothing -> do
      reportSDoc "tc.conv.assign" 30 $ sep
        [ "assigning to projected meta "
        , prettyTCM x <+> sep (map prettyTCM es) <+> text (":" ++ show dir) <+> prettyTCM v
        ]
      etaExpandMeta [Records] x
      res <- isInstantiatedMeta' x
      case res of
        Just u  -> do
          reportSDoc "tc.conv.assign" 30 $ sep
            [ "seems like eta expansion instantiated meta "
            , prettyTCM x <+> text  (":" ++ show dir) <+> prettyTCM u
            ]
          let w = u `applyE` es
          comp w v
        Nothing ->  do
          reportSLn "tc.conv.assign" 30 "eta expansion did not instantiate meta"
          patternViolation $ unblockOnMeta x -- nothing happened, give up

compareAsDir :: MonadConversion m => CompareDirection -> CompareAs -> Term -> Term -> m ()
compareAsDir dir a = dirToCmp (`compareAs'` a) dir

compareAs' :: forall m. MonadConversion m => Comparison -> CompareAs -> Term -> Term -> m ()
compareAs' cmp tt m n = case tt of
  AsTermsOf a -> compareTerm' cmp a m n
  AsSizes     -> compareSizes cmp m n
  AsTypes     -> compareAtom cmp AsTypes m n

compareTerm' :: forall m. MonadConversion m => Comparison -> Type -> Term -> Term -> m ()
compareTerm' cmp a m n =
  verboseBracket "tc.conv.term" 20 "compareTerm" $ do
  (ba, a') <- reduceWithBlocker a
  (catchConstraint (ValueCmp cmp (AsTermsOf a') m n) :: m () -> m ()) $ blockOnError ba $ do
    reportSDoc "tc.conv.term" 30 $ fsep
      [ "compareTerm", prettyTCM m, prettyTCM cmp, prettyTCM n, ":", prettyTCM a' ]
    propIrr  <- isPropEnabled
    isSize   <- isJust <$> isSizeType a'
    (bs, s)  <- reduceWithBlocker $ getSort a'
    mlvl     <- getBuiltin' builtinLevel
    reportSDoc "tc.conv.term" 40 $ fsep
      [ "compareTerm", prettyTCM m, prettyTCM cmp, prettyTCM n, ":", prettyTCM a'
      , "at sort", prettyTCM s]
    reportSDoc "tc.conv.level" 60 $ nest 2 $ sep
      [ "a'   =" <+> pretty a'
      , "mlvl =" <+> pretty mlvl
      , text $ "(Just (unEl a') == mlvl) = " ++ show (Just (unEl a') == mlvl)
      ]
    blockOnError bs $ case s of
      Prop{} | propIrr -> compareIrrelevant a' m n
      _    | isSize   -> compareSizes cmp m n
      _               -> case unEl a' of
        a | Just a == mlvl -> do
          a <- levelView m
          b <- levelView n
          equalLevel a b
        a@Pi{}    -> equalFun s a m n
        Lam _ _   -> do
          reportSDoc "tc.conv.term.sort" 10 $ fsep
            [ "compareTerm", prettyTCM m, prettyTCM cmp, prettyTCM n, ":", prettyTCM a'
            , "at sort", prettyTCM s
            ]
          __IMPOSSIBLE__
        Def r es  -> do
          isrec <- isEtaRecord r
          if isrec
            then do
              whenProfile Profile.Conversion $ tick "compare at eta record"
              sig <- getSignature

              transp <- getPrimitiveName' builtinTrans
              hcomp <- getPrimitiveName' builtinHComp

              let
                ps = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
                -- Andreas, 2010-10-11: allowing neutrals to be blocked things does not seem
                -- to change Agda's behavior
                --    isNeutral Blocked{}          = False
                isNeutral (NotBlocked _ Con{}) = return False

                -- Andreas, 2013-09-18 / 2015-06-29: a Def by copatterns is
                -- not neutral if it is blocked (there can be missing projections
                -- to trigger a reduction.
                isNeutral (NotBlocked r (Def q _)) = do    -- Andreas, 2014-12-06 optimize this using r !!
                  not <$> usesCopatterns q -- a def by copattern can reduce if projected
                isNeutral _                   = return True

                -- Amy, 2024-01-29: Is this blocked application headed by one of the
                -- cubical primitives that behave as though they are copattern matching?
                isCubicalPrimHead (NotBlocked r (Def q _)) -- Amy, 2024-01-29: optimise this using r !!
                  | Just q == transp || Just q == hcomp
                  = Just q
                isCubicalPrimHead _ = Nothing

                isMeta b = case ignoreBlocking b of
                  MetaV{} -> True
                  _       -> False

              reportSDoc "tc.conv.term" 30 $ prettyTCM a <+> "is eta record type"
              m <- reduceB m
              mNeutral <- isNeutral m
              n <- reduceB n
              nNeutral <- isNeutral n

              let
                h1 = isCubicalPrimHead m
                h2 = isCubicalPrimHead n

                mCub = isJust (isCubicalPrimHead m)
                nCub = isJust (isCubicalPrimHead n)

              when (mCub || nCub) $
                reportSDoc "tc.conv.term.cubical" 30 $ vcat
                  [ ("m (" <> prettyTCM mNeutral <> ", " <> prettyTCM mCub <> ", " <> prettyTCM h1 <> "):")
                  , nest 2 (prettyTCM m)
                  , ("n (" <> prettyTCM nNeutral <> ", " <> prettyTCM nCub <> ", " <> prettyTCM h2 <> "):")
                  , nest 2 (prettyTCM n)
                  , "at type"
                  , nest 2 (prettyTCM a')
                  , "same head:" <+> prettyTCM (h1 == h2)
                  ]

              if | isMeta m || isMeta n -> do
                     whenProfile Profile.Conversion $ tick "compare at eta-record: meta"
                     compareAtom cmp (AsTermsOf a') (ignoreBlocking m) (ignoreBlocking n)

                 -- Amy, 2024-01-29 (fixing issue pointed out by Tom Jack):
                 --
                 -- Cubical primitives reduce to something awful, so we would like to skip comparing them (causes
                 -- "timeout" in GroupPath).
                 --
                 -- We would also like to skip comparing a cubical primitive against something that is *small* and
                 -- actually neutral (causes "timeout" in KleinBottle cohomology groups, comparing a 93KiB(!) transport
                 -- against an application of set-truncation recursion to a metavariable)
                 --
                 -- The condition for skipping eta expansion is thus:
                 --   (a) both are neutrals (which in this case also includes a "suspended"/copattern transp/hcomp)
                 --   (b) if both are headed by a cubical primitive, then they are the same primitive.
                 --
                 -- So we will skip expanding transp A φ u0 = transp A' φ' u0', since it's definitionally injective; We
                 -- will skip expanding transp A φ u0 = f ?, since it's wasted work; but we will not skip
                 -- transp A φ u0 = hcomp u u0', since those must both compute if they are to be equal.
                 | mNeutral && nNeutral && (not (mCub && nCub) || h1 == h2) -> do
                     whenProfile Profile.Conversion $ tick "compare at eta-record: both neutral"
                     -- Andreas 2011-03-23: (fixing issue 396)
                     -- if we are dealing with a singleton record,
                     -- we can succeed immediately
                     let profUnitEta = whenProfile Profile.Conversion $ tick "compare at eta-record: both neutral at unit"
                     ifM (isSingletonRecordModuloRelevance r ps) profUnitEta $ do
                       -- do not eta-expand if comparing two neutrals
                       compareAtom cmp (AsTermsOf a') (ignoreBlocking m) (ignoreBlocking n)

                 | otherwise -> do
                     whenProfile Profile.Conversion $ tick "compare at eta-record: eta-expanding"
                     (tel, m') <- etaExpandRecord r ps $ ignoreBlocking m
                     (_  , n') <- etaExpandRecord r ps $ ignoreBlocking n
                     -- No subtyping on record terms
                     c <- getRecordConstructor r
                     -- Record constructors are covariant (see test/succeed/CovariantConstructors).
                     compareArgs (repeat $ polFromCmp cmp) [] (telePi_ tel __DUMMY_TYPE__) (Con c ConOSystem []) m' n'

            else (do pathview <- pathView a'
                     equalPath pathview a' m n)
        _ -> compareAtom cmp (AsTermsOf a') m n
  where
    -- equality at function type (accounts for eta)
    equalFun :: (MonadConversion m) => Sort -> Term -> Term -> Term -> m ()
    equalFun s a@(Pi dom b) m n | domIsFinite dom = do
       mp <- fmap getPrimName <$> getBuiltin' builtinIsOne
       let asFn = El s (Pi (dom { domIsFinite = False }) b)
       case unEl $ unDom dom of
          Def q [Apply phi]
              | Just q == mp -> compareTermOnFace cmp (unArg phi) asFn m n
          _                  -> equalFun s (unEl asFn) m n

    equalFun _ (Pi dom@Dom{domInfo = info} b) m n = do
        whenProfile Profile.Conversion $ tick "compare at function type"
        let name = suggests [ Suggestion b , Suggestion m , Suggestion n ]
        addContext (name, dom) $ compareTerm cmp (absBody b) m' n'
      where
        (m',n') = raise 1 (m,n) `apply` [Arg info $ var 0]

    equalFun _ _ _ _ = __IMPOSSIBLE__

    equalPath :: (MonadConversion m) => PathView -> Type -> Term -> Term -> m ()
    equalPath (PathType s _ l a x y) _ m n = do
        whenProfile Profile.Conversion $ tick "compare at path type"
        let name = "i" :: String
        interval <- el primInterval
        let (m',n') = raise 1 (m, n) `applyE` [IApply (raise 1 $ unArg x) (raise 1 $ unArg y) (var 0)]
        addContext (name, defaultDom interval) $ compareTerm cmp (El (raise 1 s) $ raise 1 (unArg a) `apply` [argN $ var 0]) m' n'
    equalPath OType{} a' m n = cmpDef a' m n

    cmpDef a'@(El s ty) m n = do
       mI     <- getBuiltinName'   builtinInterval
       mIsOne <- getBuiltinName'   builtinIsOne
       mGlue  <- getPrimitiveName' builtinGlue
       mHComp <- getPrimitiveName' builtinHComp
       mSub   <- getBuiltinName' builtinSub
       mUnglueU <- getPrimitiveTerm' builtin_unglueU
       mSubIn   <- getBuiltin' builtinSubIn
       case ty of
         Def q es | Just q == mIsOne -> return ()
         Def q es | Just q == mGlue, Just args@(l:_:a:phi:_) <- allApplyElims es -> do
              aty <- el' (pure $ unArg l) (pure $ unArg a)
              unglue <- prim_unglue
              let mkUnglue m = apply unglue $ map (setHiding Hidden) args ++ [argN m]
              reportSDoc "conv.glue" 20 $ prettyTCM (aty,mkUnglue m,mkUnglue n)

              -- Amy, 2023-01-04: Here and in hcompu below we *used to*
              -- also compare whatever the glued terms would evaluate to
              -- on φ. This is very loopy (consider φ = f i or φ = i0:
              -- both generate empty substitutions so get us back to
              -- exactly the same conversion problem)!
              --
              -- But is there a reason to do this comparison? The
              -- answer, it turns out, is no!
              --
              -- Suppose you had
              --    Γ ⊢ x = glue [φ → t] xb : Glue T S
              --    Γ ⊢ y = glue [φ → s] yb : Glue T S
              --    Γ ⊢ xb = yb : T
              -- Is there a need to check whether Γ φ ⊢ t = s : S? No!
              -- That's because the typing rule for glue is something like
              --   glue φ : (s : PartialP φ S) (t : T [ φ → s ]) → Glue T S
              -- where the bracket notation stands for an "implicit
              -- Sub"-type, i.e. Γ, φ ⊢ t = s (definitionally)
              --
              -- So if we have a glued element, and we have xb = yb, we
              -- can be sure that
              --   Γ , φ ⊢ t = xb = yb = s
              --
              -- But what about the general case, where we're not
              -- looking at a literal glue? Well, eta for Glue
              -- means x = glue [φ → x] (unglue x), so the logic above
              -- still applies. On φ, for the reducts to agree, it's
              -- enough for the bases to agree.

              compareTerm cmp aty (mkUnglue m) (mkUnglue n)
         Def q es | Just q == mHComp, Just (sl:s:args@[phi,u,u0]) <- allApplyElims es
                  , Sort (Type lvl) <- unArg s
                  , Just unglueU <- mUnglueU, Just subIn <- mSubIn
                  -> do
              let l = Level lvl
              ty <- el' (pure $ l) (pure $ unArg u0)
              let bA = subIn `apply` [sl,s,phi,u0]
              let mkUnglue m = apply unglueU $ [argH l] ++ map (setHiding Hidden) [phi,u]  ++ [argH bA,argN m]
              reportSDoc "conv.hcompU" 20 $ prettyTCM (ty,mkUnglue m,mkUnglue n)
              compareTerm cmp ty (mkUnglue m) (mkUnglue n)
         Def q es | Just q == mSub, Just args@(l:a:_) <- allApplyElims es -> do
              ty <- el' (pure $ unArg l) (pure $ unArg a)
              out <- primSubOut
              let mkOut m = apply out $ map (setHiding Hidden) args ++ [argN m]
              compareTerm cmp ty (mkOut m) (mkOut n)
         Def q [] | Just q == mI -> compareInterval cmp a' m n
         _ -> compareAtom cmp (AsTermsOf a') m n

compareAtomDir :: MonadConversion m => CompareDirection -> CompareAs -> Term -> Term -> m ()
compareAtomDir dir a = dirToCmp (`compareAtom` a) dir

-- | Compute the head type of an elimination. For projection-like functions
--   this requires inferring the type of the principal argument.
computeElimHeadType :: MonadConversion m => QName -> Elims -> Elims -> m Type
computeElimHeadType f [] es' = computeDefType f es'
computeElimHeadType f es _   = computeDefType f es

-- | Syntax directed equality on atomic values
--
compareAtom :: forall m. MonadConversion m => Comparison -> CompareAs -> Term -> Term -> m ()
compareAtom cmp t m n =
  verboseBracket "tc.conv.atom" 20 "compareAtom" $
  -- if a PatternErr is thrown, rebuild constraint!
  (catchConstraint (ValueCmp cmp t m n) :: m () -> m ()) $ do
    reportSLn "tc.conv.atom.size" 50 $ "compareAtom term size:  " ++ show (termSize m, termSize n)
    reportSDoc "tc.conv.atom" 50 $
      "compareAtom" <+> fsep [ prettyTCM m <+> prettyTCM cmp
                             , prettyTCM n
                             , prettyTCM t
                             ]
    whenProfile Profile.Conversion $ tick "compare by reduction"
    -- Are we currently defining mutual functions? Which?
    currentMutuals <- maybe (pure Set.empty) (mutualNames <.> lookupMutualBlock) =<< asksTC envMutualBlock

    -- Andreas: what happens if I cut out the eta expansion here?
    -- Answer: Triggers issue 245, does not resolve 348
    (mb',nb') <- do
      mb' <- etaExpandBlocked =<< reduceB m
      nb' <- etaExpandBlocked =<< reduceB n
      return (mb', nb')
    let blocker = unblockOnEither (getBlocker mb') (getBlocker nb')
    reportSLn "tc.conv.atom.size" 50 $ "term size after reduce: " ++ show (termSize $ ignoreBlocking mb', termSize $ ignoreBlocking nb')

    -- constructorForm changes literal to constructors
    -- only needed if the other side is not a literal
    (mb'', nb'') <- case (ignoreBlocking mb', ignoreBlocking nb') of
      (Lit _, Lit _) -> return (mb', nb')
      _ -> (,) <$> traverse constructorForm mb'
               <*> traverse constructorForm nb'

    mb <- traverse unLevel mb''
    nb <- traverse unLevel nb''

    cmpBlocked <- viewTC eCompareBlocked

    let m = ignoreBlocking mb
        n = ignoreBlocking nb

        checkDefinitionalEquality = unlessM (pureCompareAs CmpEq t m n) notEqual

        notEqual = typeError $ UnequalTerms cmp m n t

        dir = fromCmp cmp
        rid = flipCmp dir     -- The reverse direction.  Bad name, I know.

        assign dir x es v = assignE dir x es v t $ compareAsDir dir t

    reportSDoc "tc.conv.atom" 30 $
      "compareAtom" <+> fsep [ prettyTCM mb <+> prettyTCM cmp
                             , prettyTCM nb
                             , prettyTCM t
                             , prettyTCM blocker
                             ]
    reportSDoc "tc.conv.atom" 80 $
      "compareAtom" <+> fsep [ pretty mb <+> prettyTCM cmp
                                  , pretty nb
                                  , ":" <+> pretty t ]
    case (mb, nb) of
      -- equate two metas x and y.  if y is the younger meta,
      -- try first y := x and then x := y
      _ | MetaV x xArgs <- ignoreBlocking mb,   -- Can be either Blocked or NotBlocked depending on
          MetaV y yArgs <- ignoreBlocking nb -> -- envCompareBlocked check above.
        compareMetas cmp t x xArgs y yArgs

      -- one side a meta
      _ | MetaV x es <- ignoreBlocking mb -> assign dir x es n
      _ | MetaV x es <- ignoreBlocking nb -> assign rid x es m
      (Blocked{}, Blocked{}) | not cmpBlocked  -> checkDefinitionalEquality
      (Blocked b _, _) | not cmpBlocked -> useInjectivity (fromCmp cmp) b t m n   -- The blocked term  goes first
      (_, Blocked b _) | not cmpBlocked -> useInjectivity (flipCmp $ fromCmp cmp) b t n m
      bs -> do
        blockOnError blocker $ do
        -- -- Andreas, 2013-10-20 put projection-like function
        -- -- into the spine, to make compareElims work.
        -- -- 'False' means: leave (Def f []) unchanged even for
        -- -- proj-like funs.
        -- m <- elimView False m
        -- n <- elimView False n
        -- Andreas, 2015-07-01, actually, don't put them into the spine.
        -- Polarity cannot be communicated properly if projection-like
        -- functions are post-fix.
        case (m, n) of
          (Pi{}, Pi{}) -> equalFun m n

          (Sort s1, Sort s2) ->
            ifM (optCumulativity <$> pragmaOptions)
              (compareSort cmp s1 s2)
              (equalSort s1 s2)

          (Lit l1, Lit l2) | l1 == l2 -> return ()
          (Var i es, Var i' es') | i == i' -> do
              a <- typeOfBV i
              -- Variables are invariant in their arguments
              compareElims [] [] a (var i) es es'

          -- The case of definition application:
          (Def f es, Def f' es') -> do

              -- 1. All absurd lambdas are equal.
              unlessM (bothAbsurd f f') $ do

              -- 2. If the heads are unequal, the only chance is subtyping between SIZE and SIZELT.
              if f /= f' then trySizeUniv cmp t m n f es f' es' else do

              -- 3. If the heads are equal:
              -- 3a. If there are no arguments, we are done.
              unless (null es && null es') $ do

              -- 3b. If some cubical magic kicks in, we are done.
              unlessM (compareEtaPrims f es es') $ do

              -- 3c. Oh no, we actually have to work and compare the eliminations!
               a <- computeElimHeadType f es es'
               -- The polarity vector of projection-like functions
               -- does not include the parameters.
               pol <- getPolarity' cmp f
               compareElims pol [] a (Def f []) es es'

          -- Due to eta-expansion, these constructors are fully applied.
          (Con x ci xArgs, Con y _ yArgs)
              | x == y -> do
                  -- Get the type of the constructor instantiated to the datatype parameters.
                  a' <- case t of
                    AsTermsOf a -> conType x a
                    AsSizes   -> __IMPOSSIBLE__
                    AsTypes   -> __IMPOSSIBLE__
                  forcedArgs <- getForcedArgs $ conName x
                  -- Constructors are covariant in their arguments
                  -- (see test/succeed/CovariantConstructors).
                  compareElims (repeat $ polFromCmp cmp) forcedArgs a' (Con x ci []) xArgs yArgs
          _ -> notEqual
    where
        -- returns True in case we handled the comparison already.
        compareEtaPrims :: MonadConversion m => QName -> Elims -> Elims -> m Bool
        compareEtaPrims q es es' = do
          munglue <- getPrimitiveName' builtin_unglue
          munglueU <- getPrimitiveName' builtin_unglueU
          msubout <- getPrimitiveName' builtinSubOut
          case () of
            _ | Just q == munglue -> compareUnglueApp q es es'
            _ | Just q == munglueU -> compareUnglueUApp q es es'
            _ | Just q == msubout -> compareSubApp q es es'
            _                     -> return False
        compareSubApp q es es' = do
          let (as,bs) = splitAt 5 es; (as',bs') = splitAt 5 es'
          case (allApplyElims as, allApplyElims as') of
            (Just [a,bA,phi,u,x], Just [a',bA',phi',u',x']) -> do
              tSub <- primSub
              -- Andrea, 28-07-16:
              -- comparing the types is most probably wasteful,
              -- since b and b' should be neutral terms, but it's a
              -- precondition for the compareAtom call to make
              -- sense.
              equalType (El (tmSSort $ unArg a) $ apply tSub $ a : map (setHiding NotHidden) [bA,phi,u])
                        (El (tmSSort $ unArg a) $ apply tSub $ a : map (setHiding NotHidden) [bA',phi',u'])
              compareAtom cmp (AsTermsOf $ El (tmSSort $ unArg a) $ apply tSub $ a : map (setHiding NotHidden) [bA,phi,u])
                              (unArg x) (unArg x')
              compareElims [] [] (El (tmSort (unArg a)) (unArg bA)) (Def q as) bs bs'
              return True
            _  -> return False
        compareUnglueApp q es es' = do
          let (as,bs) = splitAt 7 es; (as',bs') = splitAt 7 es'
          case (allApplyElims as, allApplyElims as') of
            (Just [la,lb,bA,phi,bT,e,b], Just [la',lb',bA',phi',bT',e',b']) -> do
              tGlue <- getPrimitiveTerm builtinGlue
              -- Andrea, 28-07-16:
              -- comparing the types is most probably wasteful,
              -- since b and b' should be neutral terms, but it's a
              -- precondition for the compareAtom call to make
              -- sense.
              -- equalType (El (tmSort (unArg lb)) $ apply tGlue $ [la,lb] ++ map (setHiding NotHidden) [bA,phi,bT,e])
              --           (El (tmSort (unArg lb')) $ apply tGlue $ [la',lb'] ++ map (setHiding NotHidden) [bA',phi',bT',e'])
              compareAtom cmp (AsTermsOf $ El (tmSort (unArg lb)) $ apply tGlue $ [la,lb] ++ map (setHiding NotHidden) [bA,phi,bT,e])
                              (unArg b) (unArg b')
              compareElims [] [] (El (tmSort (unArg la)) (unArg bA)) (Def q as) bs bs'
              return True
            _  -> return False
        compareUnglueUApp :: MonadConversion m => QName -> Elims -> Elims -> m Bool
        compareUnglueUApp q es es' = do
          let (as,bs) = splitAt 5 es; (as',bs') = splitAt 5 es'
          case (allApplyElims as, allApplyElims as') of
            (Just [la,phi,bT,bAS,b], Just [la',phi',bT',bA',b']) -> do
              tHComp <- primHComp
              tLSuc <- primLevelSuc
              tSubOut <- primSubOut
              iz <- primIZero
              let lsuc t = tLSuc `apply` [argN t]
                  s = tmSort $ unArg la
                  sucla = lsuc <$> la
              bA <- runNamesT [] $ do
                la  <- open . unArg $ la
                phi <- open . unArg $ phi
                bT  <- open . unArg $ bT
                bAS <- open . unArg $ bAS
                (pure tSubOut <#> (pure tLSuc <@> la) <#> (Sort . tmSort <$> la) <#> phi <#> (bT <@> primIZero) <@> bAS)
              compareAtom cmp (AsTermsOf $ El (tmSort . unArg $ sucla) $ apply tHComp $ [sucla, argH (Sort s), phi] ++ [argH (unArg bT), argH bA])
                              (unArg b) (unArg b')
              compareElims [] [] (El s bA) (Def q as) bs bs'
              return True
            _  -> return False
        -- Andreas, 2013-05-15 due to new postponement strategy, type can now be blocked
        conType c t = do
          t <- abortIfBlocked t
          let impossible = do
                reportSDoc "impossible" 10 $
                  "expected data/record type, found " <+> prettyTCM t
                reportSDoc "impossible" 70 $ nest 2 $ "raw =" <+> pretty t
                -- __IMPOSSIBLE__
                -- Andreas, 2013-10-20:  in case termination checking fails
                -- we might get some unreduced types here.
                -- In issue 921, this happens during the final attempt
                -- to solve left-over constraints.
                -- Thus, instead of crashing, just give up gracefully.
                patternViolation neverUnblock
          maybe impossible (return . snd) =<< getFullyAppliedConType c t
        equalFun t1 t2 = case (t1, t2) of
          (Pi dom1 b1, Pi dom2 b2) -> do
            verboseBracket "tc.conv.fun" 15 "compare function types" $ do
              reportSDoc "tc.conv.fun" 20 $ nest 2 $ vcat
                [ "t1 =" <+> prettyTCM t1
                , "t2 =" <+> prettyTCM t2
                ]
              compareDom cmp dom2 dom1 b1 b2 errH errR errQ errC errP errF $
                compareType cmp (absBody b1) (absBody b2)
            where
            errH = typeError $ UnequalHiding t1 t2
            errR = typeError $ UnequalRelevance cmp t1 t2
            errQ = typeError $ UnequalQuantity  cmp t1 t2
            errC = typeError $ UnequalCohesion cmp t1 t2
            errP = typeError $ UnequalPolarity cmp t1 t2
            errF = typeError $ UnequalFiniteness cmp t1 t2
          _ -> __IMPOSSIBLE__

-- | Check whether @x xArgs `cmp` y yArgs@
compareMetas :: MonadConversion m => Comparison -> CompareAs -> MetaId -> Elims -> MetaId -> Elims -> m ()
compareMetas cmp t x xArgs y yArgs | x == y = blockOnError (unblockOnMeta x) $ do
  cmpBlocked <- viewTC eCompareBlocked
  let ok    = return ()
      notOk = patternViolation neverUnblock
      fallback = do
        -- Fallback: check definitional equality
        a <- metaType x
        runPureConversion (compareElims [] [] a (MetaV x []) xArgs yArgs) >>= \case
          Just{}  -> ok
          Nothing -> notOk
  if | cmpBlocked -> do
         a <- metaType x
         compareElims [] [] a (MetaV x []) xArgs yArgs
     | otherwise -> case intersectVars xArgs yArgs of
         -- all relevant arguments are variables
         Just kills -> do
           -- kills is a list with 'True' for each different var
           killResult <- killArgs kills x
           case killResult of
             NothingToPrune   -> ok
             PrunedEverything -> ok
             PrunedNothing    -> fallback
             PrunedSomething  -> fallback
         -- not all relevant arguments are variables
         Nothing -> fallback
compareMetas cmp t x xArgs y yArgs = do
  p1 <- getMetaPriority x
  p2 <- getMetaPriority y
  let dir = fromCmp cmp
      rid = flipCmp dir     -- The reverse direction.  Bad name, I know.
      retry = patternViolation alwaysUnblock
  -- First try the one with the highest priority. If that doesn't
  -- work, try the low priority one.
  let (solve1, solve2)
        | (p1, x) > (p2, y) = (l1, r2)
        | otherwise         = (r1, l2)
        where l1 = assignE dir x xArgs (MetaV y yArgs) t $ \ _ _ -> retry
              r1 = assignE rid y yArgs (MetaV x xArgs) t $ \ _ _ -> retry
              -- Careful: the first attempt might prune the low
              -- priority meta! (Issue #2978)
              l2 = ifM (isInstantiatedMeta x) retry l1
              r2 = ifM (isInstantiatedMeta y) retry r1

  -- Unblock on both unblockers of solve1 and solve2
  catchPatternErr (`addOrUnblocker` solve2) solve1

-- | Check whether @a1 `cmp` a2@ and continue in context extended by @a1@.
compareDom :: (MonadConversion m , Free c)
  => Comparison -- ^ @cmp@ The comparison direction
  -> Dom Type   -- ^ @a1@  The smaller domain.
  -> Dom Type   -- ^ @a2@  The other domain.
  -> Abs b      -- ^ @b1@  The smaller codomain.
  -> Abs c      -- ^ @b2@  The bigger codomain.
  -> m ()     -- ^ Continuation if mismatch in 'Hiding'.
  -> m ()     -- ^ Continuation if mismatch in 'Relevance'.
  -> m ()     -- ^ Continuation if mismatch in 'Quantity'.
  -> m ()     -- ^ Continuation if mismatch in 'Cohesion'.
  -> m ()     -- ^ Continuation if mismatch in 'Polarity'.
  -> m ()     -- ^ Continuation if mismatch in 'annFinite'.
  -> m ()     -- ^ Continuation if comparison is successful.
  -> m ()
compareDom cmp0
  dom1@(Dom{domInfo = i1, unDom = a1})
  dom2@(Dom{domInfo = i2, unDom = a2})
  b1 b2 errH errR errQ errC errP errF cont = do
  if | not $ sameHiding dom1 dom2 -> errH
     | not $ (==)         (getRelevance dom1) (getRelevance dom2) -> errR
     | not $ sameQuantity (getQuantity  dom1) (getQuantity  dom2) -> errQ
     | not $ sameCohesion (getCohesion  dom1) (getCohesion  dom2) -> errC
     | not $ samePolarity (getModalPolarity dom1) (getModalPolarity dom2) -> errP
     | not $ domIsFinite dom1 == domIsFinite dom2 -> errF
     | otherwise -> do
      let r = max (getRelevance dom1) (getRelevance dom2)
              -- take "most irrelevant"
          dependent = not (isIrrelevant r) && isBinderUsed b2
      pid <- newProblem_ $ compareType cmp0 a1 a2
      dom <- if dependent
             then (\ a -> dom1 {unDom = a}) <$> blockTypeOnProblem a1 pid
             else return dom1
        -- We only need to require a1 == a2 if b2 is dependent
        -- If it's non-dependent it doesn't matter what we add to the context.
      let name = suggests [ Suggestion b1 , Suggestion b2 ]
      addContext (name, dom) $ cont
      stealConstraints pid
        -- Andreas, 2013-05-15 Now, comparison of codomains is not
        -- blocked any more by getting stuck on domains.
        -- Only the domain type in context will be blocked.
        -- But see issue #1258.

-- | When comparing argument spines (in compareElims) where the first arguments
--   don't match, we keep going, substituting the anti-unification of the two
--   terms in the telescope. More precisely:
--
--  @@
--    (u = v : A)[pid]   w = antiUnify pid A u v   us = vs : Δ[w/x]
--    -------------------------------------------------------------
--                    u us = v vs : (x : A) Δ
--  @@
--
--   The simplest case of anti-unification is to return a fresh metavariable
--   (created by blockTermOnProblem), but if there's shared structure between
--   the two terms we can expose that.
--
--   This is really a crutch that lets us get away with things that otherwise
--   would require heterogenous conversion checking. See for instance issue
--   #2384.
antiUnify :: MonadConversion m => ProblemId -> Type -> Term -> Term -> m Term
antiUnify pid a u v = do
  SynEq.checkSyntacticEquality u v (\u _ -> return u) $ \u v -> do
  (u, v) <- reduce (u, v)
  reportSDoc "tc.conv.antiUnify" 30 $ vcat
    [ "antiUnify"
    , "a =" <+> prettyTCM a
    , "u =" <+> prettyTCM u
    , "v =" <+> prettyTCM v
    ]
  case (u, v) of
    (Pi ua ub, Pi va vb) -> do
      wa0 <- antiUnifyType pid (unDom ua) (unDom va)
      let wa = wa0 <$ ua
      wb <- addContext wa $ antiUnifyType pid (absBody ub) (absBody vb)
      return $ Pi wa (mkAbs (absName ub) wb)
    (Lam i u, Lam _ v) ->
      reduce (unEl a) >>= \case
        Pi a b -> Lam i . (mkAbs (absName u)) <$> addContext a (antiUnify pid (absBody b) (absBody u) (absBody v))
        _      -> fallback
    (Var i us, Var j vs) | i == j -> maybeGiveUp $ do
      a <- typeOfBV i
      antiUnifyElims pid a (var i) us vs
    -- Andreas, 2017-07-27:
    -- It seems that nothing guarantees here that the constructors are fully
    -- applied!?  Thus, @a@ could be a function type and we need the robust
    -- @getConType@ here.
    -- (Note that @patternViolation@ swallows exceptions coming from @getConType@
    -- thus, we would not see clearly if we used @getFullyAppliedConType@ instead.)
    (Con x ci us, Con y _ vs) | x == y -> maybeGiveUp $ do
      a <- maybe abort (return . snd) =<< getConType x a
      antiUnifyElims pid a (Con x ci []) us vs
    (Def f [], Def g []) | f == g -> return (Def f [])
    (Def f us, Def g vs) | f == g, length us == length vs -> maybeGiveUp $ do
      a <- computeElimHeadType f us vs
      antiUnifyElims pid a (Def f []) us vs
    _ -> fallback
  where
    maybeGiveUp = catchPatternErr $ \ _ -> fallback
    abort = patternViolation neverUnblock -- caught by maybeGiveUp
    fallback = blockTermOnProblem a u pid

antiUnifyArgs :: MonadConversion m => ProblemId -> Dom Type -> Arg Term -> Arg Term -> m (Arg Term)
antiUnifyArgs pid dom u v
  | not (sameModality (getModality u) (getModality v))
              = patternViolation neverUnblock
  | otherwise = applyModalityToContext u $
    ifM (isIrrelevantOrPropM dom)
    {-then-} (return u)
    {-else-} ((<$ u) <$> antiUnify pid (unDom dom) (unArg u) (unArg v))

antiUnifyType :: MonadConversion m => ProblemId -> Type -> Type -> m Type
antiUnifyType pid (El s a) (El _ b) = workOnTypes $ El s <$> antiUnify pid (sort s) a b

antiUnifyElims :: MonadConversion m => ProblemId -> Type -> Term -> Elims -> Elims -> m Term
antiUnifyElims pid a self [] [] = return self
antiUnifyElims pid a self (Proj o f : es1) (Proj _ g : es2) | f == g = do
  res <- projectTyped self a o f
  case res of
    Just (_, self, a) -> antiUnifyElims pid a self es1 es2
    Nothing -> patternViolation neverUnblock -- can fail for projection like
antiUnifyElims pid a self (Apply u : es1) (Apply v : es2) = do
  reduce (unEl a) >>= \case
    Pi a b -> do
      w <- antiUnifyArgs pid a u v
      antiUnifyElims pid (b `lazyAbsApp` unArg w) (apply self [w]) es1 es2
    _ -> patternViolation neverUnblock
antiUnifyElims _ _ _ _ _ = patternViolation neverUnblock -- trigger maybeGiveUp in antiUnify

-- | @compareElims pols a v els1 els2@ performs type-directed equality on eliminator spines.
--   @t@ is the type of the head @v@.
compareElims :: forall m. MonadConversion m => [Polarity] -> [IsForced] -> Type -> Term -> [Elim] -> [Elim] -> m ()
compareElims pols0 fors0 a v els01 els02 =
  verboseBracket "tc.conv.elim" 20 "compareElims" $
  (catchConstraint (ElimCmp pols0 fors0 a v els01 els02) :: m () -> m ()) $ do
  let v1 = applyE v els01
      v2 = applyE v els02
      failure = typeError $ UnequalTerms CmpEq v1 v2 (AsTermsOf a)
        -- Andreas, 2013-03-15 since one of the spines is empty, @a@
        -- is the correct type here.
  unless (null els01) $ do
    reportSDoc "tc.conv.elim" 25 $ "compareElims" $$ do
     nest 2 $ vcat
      [ "a     =" <+> prettyTCM a
      , "pols0 (truncated to 10) =" <+> hsep (map prettyTCM $ take 10 pols0)
      , "fors0 (truncated to 10) =" <+> hsep (map prettyTCM $ take 10 fors0)
      , "v     =" <+> prettyTCM v
      , "els01 =" <+> prettyTCM els01
      , "els02 =" <+> prettyTCM els02
      ]
  case (els01, els02) of
    ([]         , []         ) -> return ()
    ([]         , Proj{}:_   ) -> failure -- not impossible, see issue 821
    (Proj{}  : _, []         ) -> failure -- could be x.p =?= x for projection p
    ([]         , Apply{} : _) -> failure -- not impossible, see issue 878
    (Apply{} : _, []         ) -> failure
    ([]         , IApply{} : _) -> failure
    (IApply{} : _, []         ) -> failure
    (Apply{} : _, Proj{}  : _) -> __IMPOSSIBLE__ <$ solveAwakeConstraints' True -- NB: popped up in issue 889
    (Proj{}  : _, Apply{} : _) -> __IMPOSSIBLE__ <$ solveAwakeConstraints' True -- but should be impossible (but again in issue 1467)
    (IApply{} : _, Proj{}  : _) -> __IMPOSSIBLE__ <$ solveAwakeConstraints' True
    (Proj{}  : _, IApply{} : _) -> __IMPOSSIBLE__ <$ solveAwakeConstraints' True
    (IApply{} : _, Apply{}  : _) -> __IMPOSSIBLE__ <$ solveAwakeConstraints' True
    (Apply{}  : _, IApply{} : _) -> __IMPOSSIBLE__ <$ solveAwakeConstraints' True
    (e@(IApply x1 y1 r1) : els1, IApply x2 y2 r2 : els2) -> do
      reportSDoc "tc.conv.elim" 25 $ "compareElims IApply"
       -- Andrea: copying stuff from the Apply case..
      let (pol, pols) = nextPolarity pols0
      a  <- abortIfBlocked a
      va <- pathView a
      reportSDoc "tc.conv.elim.iapply" 60 $ "compareElims IApply" $$ do
        nest 2 $ "va =" <+> text (show (isPathType va))
      case va of
        PathType s path l bA x y -> do
          b <- primIntervalType
          compareWithPol pol (flip compareTerm b)
                              r1 r2
          -- TODO: compare (x1,x2) and (y1,y2) ?
          let r = r1 -- TODO Andrea:  do blocking
          codom <- el' (pure . unArg $ l) ((pure . unArg $ bA) <@> pure r)
          compareElims pols [] codom -- Path non-dependent (codom `lazyAbsApp` unArg arg)
                            (applyE v [e]) els1 els2
        -- We allow for functions (i : I) -> ... to also be heads of a IApply,
        -- because @etaContract@ can produce such terms
        OType t@(El _ Pi{}) -> compareElims pols0 fors0 t v (Apply (defaultArg r1) : els1) (Apply (defaultArg r2) : els2)

        OType t -> patternViolation (unblockOnAnyMetaIn t) -- Can we get here? We know a is not blocked.

    (Apply arg1 : els1, Apply arg2 : els2) ->
      (verboseBracket "tc.conv.elim" 20 "compare Apply" :: m () -> m ()) $ do
      reportSDoc "tc.conv.elim" 10 $ nest 2 $ vcat
        [ "a    =" <+> prettyTCM a
        , "v    =" <+> prettyTCM v
        , "arg1 =" <+> prettyTCM arg1
        , "arg2 =" <+> prettyTCM arg2
        ]
      reportSDoc "tc.conv.elim" 50 $ nest 2 $ vcat
        [ "raw:"
        , "a    =" <+> pretty a
        , "v    =" <+> pretty v
        , "arg1 =" <+> pretty arg1
        , "arg2 =" <+> pretty arg2
        ]
      let (pol, pols) = nextPolarity pols0
          (for, fors) = nextIsForced fors0
      a <- abortIfBlocked a
      reportSLn "tc.conv.elim" 40 $ "type is not blocked"
      case unEl a of
        (Pi (Dom{domInfo = info, unDom = b}) codom) -> do
          reportSLn "tc.conv.elim" 40 $ "type is a function type"
          mlvl <- tryMaybe primLevel
          let freeInCoDom (Abs _ c) = 0 `freeInIgnoringSorts` c
              freeInCoDom _         = False
              dependent = (Just (unEl b) /= mlvl) && freeInCoDom codom
                -- Level-polymorphism (x : Level) -> ... does not count as dependency here
                   -- NB: we could drop the free variable test and still be sound.
                   -- It is a trade-off between the administrative effort of
                   -- creating a blocking and traversing a term for free variables.
                   -- Apparently, it is believed that checking free vars is cheaper.
                   -- Andreas, 2013-05-15

-- NEW, Andreas, 2013-05-15

          -- compare arg1 and arg2
          pid <- newProblem_ $ applyModalityToContext info $
              if isForced for then
                reportSLn "tc.conv.elim" 40 $ "argument is forced"
              else if isIrrelevant info then do
                reportSLn "tc.conv.elim" 40 $ "argument is irrelevant"
                compareIrrelevant b (unArg arg1) (unArg arg2)
              else do
                reportSLn "tc.conv.elim" 40 $ "argument has polarity " ++ show pol
                compareWithPol pol (flip compareTerm b)
                  (unArg arg1) (unArg arg2)
          -- if comparison got stuck and function type is dependent, block arg
          solved <- isProblemSolved pid
          reportSLn "tc.conv.elim" 40 $ "solved = " ++ show solved
          arg <- if dependent && not solved
                 then applyModalityToContext info $ do
                  reportSDoc "tc.conv.elims" 50 $ vcat $
                    [ "Trying antiUnify:"
                    , nest 2 $ "b    =" <+> prettyTCM b
                    , nest 2 $ "arg1 =" <+> prettyTCM arg1
                    , nest 2 $ "arg2 =" <+> prettyTCM arg2
                    ]
                  arg <- (arg1 $>) <$> antiUnify pid b (unArg arg1) (unArg arg2)
                  reportSDoc "tc.conv.elims" 50 $ hang "Anti-unification:" 2 (prettyTCM arg)
                  reportSDoc "tc.conv.elims" 70 $ nest 2 $ "raw:" <+> pretty arg
                  return arg
                 else return arg1
          -- continue, possibly with blocked instantiation
          compareElims pols fors (codom `lazyAbsApp` unArg arg) (apply v [arg]) els1 els2
          -- any left over constraints of arg are associated to the comparison
          reportSLn "tc.conv.elim" 40 $ "stealing constraints from problem " ++ show pid
          stealConstraints pid
          {- Stealing solves this issue:

             Does not create enough blocked tc-problems,
             see test/fail/DontPrune.
             (There are remaining problems which do not show up as yellow.)
             Need to find a way to associate pid also to result of compareElims.
          -}
        a -> do
          reportSDoc "impossible" 10 $
            "unexpected type when comparing apply eliminations " <+> prettyTCM a
          reportSDoc "impossible" 50 $ "raw type:" <+> pretty a
          patternViolation (unblockOnAnyMetaIn a)
          -- Andreas, 2013-10-22
          -- in case of disabled reductions (due to failing termination check)
          -- we might get stuck, so do not crash, but fail gently.
          -- __IMPOSSIBLE__

    -- case: f == f' are projections
    (Proj o f : els1, Proj _ f' : els2)
      | f /= f'   -> typeError $ MismatchedProjectionsError f f'
      | otherwise -> do
        a   <- abortIfBlocked a
        res <- projectTyped v a o f -- fails only if f is proj.like but parameters cannot be retrieved
        case res of
          Just (_, u, t) -> do
            -- Andreas, 2015-07-01:
            -- The arguments following the principal argument of a projection
            -- are invariant.  (At least as long as we have no explicit polarity
            -- annotations.)
            compareElims [] [] t u els1 els2
          Nothing -> do
            reportSDoc "tc.conv.elims" 30 $ sep
              [ text $ "projection " ++ prettyShow f
              , text   "applied to value " <+> prettyTCM v
              , text   "of unexpected type " <+> prettyTCM a
              ]
            patternViolation (unblockOnAnyMetaIn a)


-- | "Compare" two terms in irrelevant position.  This always succeeds.
--   However, we can dig for solutions of irrelevant metas in the
--   terms we compare.
--   (Certainly not the systematic solution, that'd be proof search...)
compareIrrelevant :: MonadConversion m => Type -> Term -> Term -> m ()
{- 2012-04-02 DontCare no longer present
compareIrrelevant t (DontCare v) w = compareIrrelevant t v w
compareIrrelevant t v (DontCare w) = compareIrrelevant t v w
-}
compareIrrelevant t v0 w0 = do
  let v = stripDontCare v0
      w = stripDontCare w0
  reportSDoc "tc.conv.irr" 20 $ vcat
    [ "compareIrrelevant"
    , nest 2 $ "v =" <+> prettyTCM v
    , nest 2 $ "w =" <+> prettyTCM w
    ]
  reportSDoc "tc.conv.irr" 50 $ vcat
    [ nest 2 $ "v =" <+> pretty v
    , nest 2 $ "w =" <+> pretty w
    ]
  whenProfile Profile.Conversion $ tick "compare irrelevant"
  try v w $ try w v $ return ()
  where
    try (MetaV x es) w fallback = do
      mi <- lookupMetaInstantiation x
      mm <- lookupMetaModality x
      let rel  = getRelevance mm
          inst = case mi of
                   InstV{} -> True
                   _       -> False
      reportSDoc "tc.conv.irr" 20 $ vcat
        [ nest 2 $ text $ "rel  = " ++ show rel
        , nest 2 $ "inst =" <+> pretty inst
        ]
      if not (isIrrelevant rel) || inst
        then fallback
        -- Andreas, 2016-08-08, issue #2131:
        -- Mining for solutions for irrelevant metas is not definite.
        -- Thus, in case of error, leave meta unsolved.
        else assignE DirEq x es w (AsTermsOf t) (compareIrrelevant t) `catchError` \ _ -> fallback
        -- the value of irrelevant or unused meta does not matter
    try v w fallback = fallback

compareWithPol :: MonadConversion m => Polarity -> (Comparison -> a -> a -> m ()) -> a -> a -> m ()
compareWithPol Invariant     cmp x y = cmp CmpEq x y
compareWithPol Covariant     cmp x y = cmp CmpLeq x y
compareWithPol Contravariant cmp x y = cmp CmpLeq y x
compareWithPol Nonvariant    cmp x y = return ()

polFromCmp :: Comparison -> Polarity
polFromCmp CmpLeq = Covariant
polFromCmp CmpEq  = Invariant

-- | Type-directed equality on argument lists
--
compareArgs :: MonadConversion m => [Polarity] -> [IsForced] -> Type -> Term -> Args -> Args -> m ()
compareArgs pol for a v args1 args2 =
  compareElims pol for a v (map Apply args1) (map Apply args2)

---------------------------------------------------------------------------
-- * Types
---------------------------------------------------------------------------

{-# SPECIALIZE compareType :: Comparison -> Type -> Type -> TCM () #-}
-- | Equality on Types
compareType :: MonadConversion m => Comparison -> Type -> Type -> m ()
compareType cmp ty1@(El s1 a1) ty2@(El s2 a2) =
    workOnTypes $
    verboseBracket "tc.conv.type" 20 "compareType" $ do
        reportSDoc "tc.conv.type" 50 $ vcat
          [ "compareType" <+> sep [ prettyTCM ty1 <+> prettyTCM cmp
                                       , prettyTCM ty2 ]
          , hsep [ "   sorts:", prettyTCM s1, " and ", prettyTCM s2 ]
          ]
        compareAs cmp AsTypes a1 a2

leqType :: MonadConversion m => Type -> Type -> m ()
leqType = compareType CmpLeq

{-# SPECIALIZE coerce :: Comparison -> Term -> Type -> Type -> TCM Term #-}
-- | @coerce v a b@ coerces @v : a@ to type @b@, returning a @v' : b@
--   with maybe extra hidden applications or hidden abstractions.
--
--   In principle, this function can host coercive subtyping, but
--   currently it only tries to fix problems with hidden function types.
--
coerce :: (MonadConversion m, MonadTCM m) => Comparison -> Term -> Type -> Type -> m Term
coerce cmp v t1 t2 = blockTerm t2 $ do
  verboseS "tc.conv.coerce" 10 $ do
    (a1,a2) <- reify (t1,t2)
    let dbglvl = 30
    reportSDoc "tc.conv.coerce" dbglvl $
      "coerce" <+> vcat
        [ "term      v  =" <+> prettyTCM v
        , "from type t1 =" <+> prettyTCM a1
        , "to type   t2 =" <+> prettyTCM a2
        , "comparison   =" <+> prettyTCM cmp
        ]
    reportSDoc "tc.conv.coerce" 70 $
      "coerce" <+> vcat
        [ "term      v  =" <+> pretty v
        , "from type t1 =" <+> pretty t1
        , "to type   t2 =" <+> pretty t2
        , "comparison   =" <+> pretty cmp
        ]
  -- v <$ do workOnTypes $ leqType t1 t2
  -- take off hidden/instance domains from t1 and t2
  TelV tel1 b1 <- telViewUpTo' (-1) notVisible t1
  TelV tel2 b2 <- telViewUpTo' (-1) notVisible t2
  let n = size tel1 - size tel2
  -- the crude solution would be
  --   v' = λ {tel2} → v {tel1}
  -- however, that may introduce unneccessary many function types
  -- If n  > 0 and b2 is not blocked, it is safe to
  -- insert n many hidden args
  if n <= 0 then fallback else do
    ifBlocked b2 (\ _ _ -> fallback) $ \ _ _ -> do
      (args, t1') <- implicitArgs n notVisible t1
      let v' = v `apply` args
      v' <$ coerceSize (compareType cmp) v' t1' t2
  where
    fallback = v <$ coerceSize (compareType cmp) v t1 t2

{-# SPECIALIZE coerceSize :: (Type -> Type -> TCM ()) -> Term -> Type -> Type -> TCM () #-}
-- | Account for situations like @k : (Size< j) <= (Size< k + 1)@
--
--   Actually, the semantics is
--   @(Size<= k) ∩ (Size< j) ⊆ rhs@
--   which gives a disjunctive constraint.  Mmmh, looks like stuff
--   TODO.
--
--   For now, we do a cheap heuristics.
--
coerceSize :: MonadConversion m => (Type -> Type -> m ()) -> Term -> Type -> Type -> m ()
coerceSize leqType v t1 t2 = verboseBracket "tc.conv.size.coerce" 45 "coerceSize" $
  workOnTypes $ do
    reportSDoc "tc.conv.size.coerce" 70 $
      "coerceSize" <+> vcat
        [ "term      v  =" <+> pretty v
        , "from type t1 =" <+> pretty t1
        , "to type   t2 =" <+> pretty t2
        ]
    let fallback = leqType t1 t2
        done = caseMaybeM (isSizeType =<< reduce t1) fallback $ \ _ -> return ()
    -- Andreas, 2015-07-22, Issue 1615:
    -- If t1 is a meta and t2 a type like Size< v2, we need to make sure we do not miss
    -- the constraint v < v2!
    caseMaybeM (isSizeType =<< reduce t2) fallback $ \ b2 -> do
      -- Andreas, 2017-01-20, issue #2329:
      -- If v is not a size suitable for the solver, like a neutral term,
      -- we can only rely on the type.
      mv <- sizeMaxView v
      if any (\case{ DOtherSize{} -> True; _ -> False }) mv then fallback else do
      -- Andreas, 2015-02-11 do not instantiate metas here (triggers issue 1203).
      unlessM (tryConversion $ dontAssignMetas $ leqType t1 t2) $ do
        -- A (most probably weaker) alternative is to just check syn.eq.
        -- ifM (snd <$> checkSyntacticEquality t1 t2) (return v) $ {- else -} do
        reportSDoc "tc.conv.size.coerce" 20 $ "coercing to a size type"
        case b2 of
          -- @t2 = Size@.  We are done!
          BoundedNo -> done
          -- @t2 = Size< v2@
          BoundedLt v2 -> do
            sv2 <- sizeView v2
            case sv2 of
              SizeInf     -> done
              OtherSize{} -> do
                -- Andreas, 2014-06-16:
                -- Issue 1203: For now, just treat v < v2 as suc v <= v2
                -- TODO: Need proper < comparison
                vinc <- sizeSuc 1 v
                compareSizes CmpLeq vinc v2
                done
              -- @v2 = a2 + 1@: In this case, we can try @v <= a2@
              SizeSuc a2 -> do
                compareSizes CmpLeq v a2
                done  -- to pass Issue 1136

---------------------------------------------------------------------------
-- * Sorts and levels
---------------------------------------------------------------------------

compareLevel :: MonadConversion m => Comparison -> Level -> Level -> m ()
compareLevel CmpLeq u v = leqLevel u v
compareLevel CmpEq  u v = equalLevel u v

compareSort :: MonadConversion m => Comparison -> Sort -> Sort -> m ()
compareSort CmpEq  = equalSort
compareSort CmpLeq = leqSort

-- | Check that the first sort is less or equal to the second.
--
--   We can put @SizeUniv@ below @Inf@, but otherwise, it is
--   unrelated to the other universes.
--
leqSort :: forall m. MonadConversion m => Sort -> Sort -> m ()
leqSort s1 s2 = do
  reportSDoc "tc.conv.sort" 30 $
    sep [ "leqSort"
        , nest 2 $ fsep [ prettyTCM s1 <+> "=<"
                        , prettyTCM s2 ]
        ]
  reportSDoc "tc.conv.sort" 60 $
    sep [ "leqSort"
        , nest 2 $ fsep [ pretty s1 <+> "=<"
                        , pretty s2 ]
        ]
  whenProfile Profile.Conversion $ tick "compare sorts"

  SynEq.checkSyntacticEquality s1 s2 (\_ _ -> return ()) $ \s1 s2 -> do

    s1b <- reduceB s1
    s2b <- reduceB s2

    let (s1,s2) = (ignoreBlocking s1b , ignoreBlocking s2b)
        blocker = unblockOnEither (getBlocker s1b) (getBlocker s2b)
        postpone = patternViolation blocker

    let postponeIfBlocked = catchPatternErr $ \blocker -> do
          if | blocker == neverUnblock -> typeError $ NotLeqSort s1 s2
             | otherwise -> do
                 reportSDoc "tc.conv.sort" 30 $ vcat
                   [ "Postponing constraint"
                   , nest 2 $ fsep [ prettyTCM s1 <+> "=<"
                                   , prettyTCM s2 ]
                   ]
                 reportSDoc "tc.conv.sort" 60 $ vcat
                   [ "Postponing constraint"
                   , nest 2 $ fsep [ pretty s1 <+> "=<"
                                   , pretty s2 ]
                   ]
                 blocker <- updateBlocker blocker
                 addConstraint blocker $ SortCmp CmpLeq s1 s2

    propEnabled <- isPropEnabled
    typeInTypeEnabled <- typeInType
    omegaInOmegaEnabled <- optOmegaInOmega <$> pragmaOptions
    let infInInf = typeInTypeEnabled || omegaInOmegaEnabled

    let fvsRHS = (`IntSet.member` allFreeVars s2)
    badRigid <- s1 `rigidVarsNotContainedIn` fvsRHS

    postponeIfBlocked $ case (s1, s2) of
      -- Andreas, 2018-09-03: crash on dummy sort
      (DummyS s, _) -> impossibleSort s
      (_, DummyS s) -> impossibleSort s

      -- The most basic rule: @Set l =< Set l'@ iff @l =< l'@
      -- Likewise for @Prop@
      -- Likewise for @SSet@
      -- @Prop l@ is below @Set l@
      -- @Set l@ is below @SSet l@
      -- @Prop l@ is below @SSet l@
      (Univ u a, Univ u' b) -> if u <= u' then leqLevel a b else no

      -- @Setωᵢ@ is above all small sorts
      (Inf u m , Inf u' n) -> answer $ u <= u' && (m <= n || infInInf)
      (Univ u _, Inf u' _) -> answer $ u <= u'
      (Inf u _, Univ u' _) -> answer $ u == u' && typeInTypeEnabled

      -- @LockUniv@, @LevelUniv@, @IntervalUniv@, @SizeUniv@, and @Prop0@ are bottom sorts.
      -- So is @Set0@ if @Prop@ is not enabled.
      (_       , LockUniv) -> equalSort s1 s2
      (_       , LevelUniv) -> equalSort s1 s2
      (_       , IntervalUniv) -> equalSort s1 s2
      (_       , SizeUniv) -> equalSort s1 s2
      (_       , Prop (Max 0 [])) -> equalSort s1 s2
      (_       , Type (Max 0 []))
        | not propEnabled  -> equalSort s1 s2

      -- @SizeUniv@, @LockUniv@ and @LevelUniv@ are unrelated to any @Set l@ or @Prop l@
      (SizeUniv, Univ{}  ) -> no
      (SizeUniv , Inf{}  ) -> no
      (LockUniv, Univ{}  ) -> no
      (LockUniv , Inf{}  ) -> no
      (LevelUniv, Univ{}  ) -> no
      (LevelUniv , Inf{}  ) -> no

      -- @IntervalUniv@ is below @SSet l@, but not @Set l@ or @Prop l@
      (IntervalUniv, Type{}) -> no
      (IntervalUniv, Prop{}) -> no
      (IntervalUniv , Inf u _) -> answer $ univFibrancy u == IsStrict
      (IntervalUniv , SSet b) -> leqLevel (ClosedLevel 0) b

      -- If the first sort is a small sort that rigidly depends on a
      -- variable and the second sort does not mention this variable,
      -- the second sort must be at least @Setω@.
      (_       , _       ) | Right (SmallSort f) <- sizeOfSort s1 , badRigid -> leqSort (Inf f 0) s2

      -- PiSort, FunSort, UnivSort and MetaS might reduce once we instantiate
      -- more metas, so we postpone.
      (PiSort{}, _       ) -> postpone
      (_       , PiSort{}) -> postpone
      (FunSort{}, _      ) -> postpone
      (_      , FunSort{}) -> postpone
      (UnivSort{}, _     ) -> postpone
      (_     , UnivSort{}) -> postpone
      (MetaS{} , _       ) -> postpone
      (_       , MetaS{} ) -> postpone

      -- DefS are postulated sorts, so they do not reduce.
      (DefS{} , _     ) -> no
      (_      , DefS{}) -> no

  where
  no  = patternViolation neverUnblock
  yes = return ()
  answer = \case
    True -> yes
    False -> no
  impossibleSort s = do
    reportS "impossible" 10
      [ "leqSort: found dummy sort with description:"
      , s
      ]
    __IMPOSSIBLE__

leqLevel :: MonadConversion m => Level -> Level -> m ()
leqLevel a b = catchConstraint (LevelCmp CmpLeq a b) $ do
      reportSDoc "tc.conv.level" 30 $
        "compareLevel" <+>
          sep [ prettyTCM a <+> "=<"
              , prettyTCM b ]
      whenProfile Profile.Conversion $ tick "compare levels"

      (a, b) <- normalise (a, b)
      SynEq.checkSyntacticEquality' a b
        (\_ _ ->
          reportSDoc "tc.conv.level" 60
            "checkSyntacticEquality returns True") $ \a b -> do
      reportSDoc "tc.conv.level" 60
        "checkSyntacticEquality returns False"

      let notok    = unlessM typeInType $ typeError $ NotLeqSort (Type a) (Type b)
          postpone = patternViolation (unblockOnAnyMetaIn (a, b))

          wrap m = m `catchError` \case
            TypeError{} -> notok
            err         -> throwError err

      cumulativity <- optCumulativity <$> pragmaOptions
      areWeComputingOverlap <- viewTC eConflComputingOverlap
      reportSDoc "tc.conv.level" 40 $
        "compareLevelView" <+>
          sep [ prettyList_ $ fmap (pretty . unSingleLevel) $ levelMaxView a
              , "=<"
              , prettyList_ $ fmap (pretty . unSingleLevel) $ levelMaxView b
              ]

      -- Extra reduce on level atoms, but should be cheap since they are already reduced.
      aB <- mapM reduceB a
      bB <- mapM reduceB b

      wrap $ case (levelMaxView aB, levelMaxView bB) of

        -- 0 ≤ any
        (SingleClosed 0 :| [] , _) -> return ()

        -- any ≤ 0
        (as , SingleClosed 0 :| []) ->
          forM_ as $ \ a' -> equalLevel (unSingleLevel $ fmap ignoreBlocking a') (ClosedLevel 0)

        -- closed ≤ closed
        (SingleClosed m :| [], SingleClosed n :| []) -> unless (m <= n) notok

        -- closed ≤ b
        (SingleClosed m :| [] , _)
          | m <= levelLowerBound b -> return ()

        -- as ≤ neutral/closed
        (as, bs)
          | all neutralOrClosed bs , levelLowerBound a > levelLowerBound b -> notok

        -- ⊔ as ≤ single
        (as@(_ :| _ : _), b :| []) ->
          forM_ as $ \ a' -> leqLevel (unSingleLevel $ ignoreBlocking <$> a')
                                      (unSingleLevel $ ignoreBlocking <$> b)

        -- reduce constants
        (as, bs)
          | let minN = min (fst $ levelPlusView a) (fst $ levelPlusView b)
                a'   = fromMaybe __IMPOSSIBLE__ $ subLevel minN a
                b'   = fromMaybe __IMPOSSIBLE__ $ subLevel minN b
          , minN > 0 -> leqLevel a' b'

        -- remove subsumed
        -- Andreas, 2014-04-07: This is ok if we do not go back to equalLevel
        (as, bs)
          | (subsumed@(_:_) , as') <- List1.partition (isSubsumed . fmap ignoreBlocking) as
          -> leqLevel (unSingleLevels $ (fmap . fmap) ignoreBlocking as') b
          where
            isSubsumed a = any (`subsumes` a) $ (fmap . fmap) ignoreBlocking bs

            subsumes :: SingleLevel -> SingleLevel -> Bool
            subsumes (SingleClosed m)        (SingleClosed n)        = m >= n
            subsumes (SinglePlus (Plus m _)) (SingleClosed n)        = m >= n
            subsumes (SinglePlus (Plus m a)) (SinglePlus (Plus n b)) = a == b && m >= n
            subsumes _ _ = False

        -- as ≤ _l x₁ .. xₙ ⊔ bs
        -- We can solve _l := λ x₁ .. xₙ -> as ⊔ (_l' x₁ .. xₙ)
        -- (where _l' is a new metavariable)
        (as , bs)
          | cumulativity
          , not areWeComputingOverlap
          , Just (mb@(MetaV x es) , bs') <- singleMetaView $ (map . fmap) ignoreBlocking (List1.toList bs)
          , null bs' || noMetas (Level a , unSingleLevels bs') -> do
            mv <- lookupLocalMeta x
            -- Jesper, 2019-10-13: abort if this is an interaction
            -- meta or a generalizable meta
            abort <- (isJust <$> isInteractionMeta x) `or2M`
                     ((== YesGeneralizeVar) <$> isGeneralizableMeta x)
            if | abort -> postpone
               | otherwise -> do
                  x' <- case mvJudgement mv of
                    IsSort{} -> __IMPOSSIBLE__
                    HasType _ cmp t -> do
                      TelV tel t' <- telView t
                      newMeta Instantiable (mvInfo mv) normalMetaPriority (idP $ size tel) $ HasType () cmp t
                  reportSDoc "tc.conv.level" 20 $ fsep
                    [ "attempting to solve" , prettyTCM (MetaV x es) , "to the maximum of"
                    , prettyTCM (Level a) , "and the fresh meta" , prettyTCM (MetaV x' es)
                    ]
                  equalLevel (atomicLevel mb) $ levelLub a (atomicLevel $ MetaV x' es)


        -- Andreas, 2016-09-28: This simplification loses the solution lzero.
        -- Thus, it is invalid.
        -- See test/Succeed/LevelMetaLeqNeutralLevel.agda.
        -- -- [a] ≤ [neutral]
        -- ([a@(Plus n _)], [b@(Plus m NeutralLevel{})])
        --   | m == n -> equalLevel' (Max [a]) (Max [b])
        --   -- Andreas, 2014-04-07: This call to equalLevel is ok even if we removed
        --   -- subsumed terms from the lhs.

        -- anything else
        _ | noMetas (a, b) -> notok
          | otherwise      -> postpone
      where
        neutralOrClosed (SingleClosed _)                   = True
        neutralOrClosed (SinglePlus (Plus _ NotBlocked{})) = True
        neutralOrClosed _                                  = False

        -- Is there exactly one @MetaV@ in the list of single levels?
        singleMetaView :: [SingleLevel] -> Maybe (Term, [SingleLevel])
        singleMetaView (SinglePlus (Plus 0 l@(MetaV m es)) : ls)
          | all (not . isMetaLevel) ls = Just (l,ls)
        singleMetaView (l : ls)
          | not $ isMetaLevel l = second (l:) <$> singleMetaView ls
        singleMetaView _ = Nothing

        isMetaLevel :: SingleLevel -> Bool
        isMetaLevel (SinglePlus (Plus _ MetaV{})) = True
        isMetaLevel _                             = False

{-# SPECIALIZE equalLevel :: Level -> Level -> TCM () #-}
equalLevel :: forall m. MonadConversion m => Level -> Level -> m ()
equalLevel a b = do
  reportSDoc "tc.conv.level" 50 $ sep [ "equalLevel", nest 2 $ parens $ pretty a, nest 2 $ parens $ pretty b ]
  whenProfile Profile.Conversion $ tick "compare levels"
  -- Andreas, 2013-10-31 remove common terms (that don't contain metas!)
  -- THAT's actually UNSOUND when metas are instantiated, because
  --     max a b == max a c  does not imply  b == c
  -- as <- return $ Set.fromList $ closed0 as
  -- bs <- return $ Set.fromList $ closed0 bs
  -- let cs = Set.filter (not . hasMeta) $ Set.intersection as bs
  -- as <- return $ Set.toList $ as Set.\\ cs
  -- bs <- return $ Set.toList $ bs Set.\\ cs

  reportSDoc "tc.conv.level" 40 $
    sep [ "equalLevel"
        , vcat [ nest 2 $ sep [ prettyTCM a <+> "=="
                              , prettyTCM b
                              ]
               ]
        ]
  reportSDoc "tc.conv.level" 80 $ sep [ "equalLevel", nest 2 $ parens $ pretty a, nest 2 $ parens $ pretty b ]

  (a, b) <- normalise (a, b)

  -- Jesper, 2014-02-02 remove terms that certainly do not contribute
  -- to the maximum
  let (a', b') = removeSubsumed a b

  SynEq.checkSyntacticEquality' a' b'
    (\_ _ ->
      reportSDoc "tc.conv.level" 60
        "checkSyntacticEquality returns True") $ \a b -> do

  reportSDoc "tc.conv.level" 60 "checkSyntacticEquality returns False"

  let notok    = unlessM typeInType notOk
      notOk    = typeError $ UnequalLevel CmpEq a' b'
      postpone = do
        reportSDoc "tc.conv.level" 30 $ hang "postponing:" 2 $ hang (pretty a' <+> "==") 0 (pretty b')
        blocker <- unblockOnAnyMetaIn <$> instantiateFull (a', b')
        patternViolation blocker

  reportSDoc "tc.conv.level" 50 $
    sep [ "equalLevel (w/o subsumed)"
        , vcat [ nest 2 $ sep [ prettyTCM a' <+> "=="
                              , prettyTCM b'
                              ]
               ]
        ]

  let as  = levelMaxView a'
      bs  = levelMaxView b'
  reportSDoc "tc.conv.level" 50 $
    sep [ text "equalLevel"
        , vcat [ nest 2 $ sep [ prettyList_ $ fmap (prettyTCM . unSingleLevel) as
                              , "=="
                              , prettyList_ $ fmap (prettyTCM . unSingleLevel) bs
                              ]
               ]
        ]

  reportSDoc "tc.conv.level" 80 $
    sep [ text "equalLevel"
        , vcat [ nest 2 $ sep [ prettyList_ $ fmap (pretty . unSingleLevel) as
                              , "=="
                              , prettyList_ $ fmap (pretty . unSingleLevel) bs
                              ]
               ]
        ]

  -- Extra reduce on level atoms, but should be cheap since they are already reduced.
  as <- (mapM . mapM) reduceB as
  bs <- (mapM . mapM) reduceB bs

  catchConstraint (LevelCmp CmpEq a b) $ case (as, bs) of

        -- closed == closed
        (SingleClosed m :| [], SingleClosed n :| [])
          | m == n    -> return ()
          | otherwise -> notok

        -- closed == neutral
        (SingleClosed m :| [] , bs) | any isNeutral bs -> notok
        (as , SingleClosed n :| []) | any isNeutral as -> notok

        -- closed == b
        (SingleClosed m :| [] , _) | m < levelLowerBound b -> notok
        (_ , SingleClosed n :| []) | n < levelLowerBound a -> notok

        -- 0 == a ⊔ b
        (SingleClosed 0 :| [] , bs@(_ :| _ : _)) ->
          forM_ bs $ \ b' ->  equalLevel (ClosedLevel 0) (unSingleLevel $ ignoreBlocking <$> b')
        (as@(_ :| _ : _) , SingleClosed 0 :| []) ->
          forM_ as $ \ a' -> equalLevel (unSingleLevel $ ignoreBlocking <$> a') (ClosedLevel 0)

        -- meta == any
        (SinglePlus (Plus k a) :| [] , SinglePlus (Plus l b) :| [])
          -- there is only a potential choice when k == l
          | MetaV x as' <- ignoreBlocking a
          , MetaV y bs' <- ignoreBlocking b
          , k == l -> do
              lvl <- levelType'
              compareMetas CmpEq (AsTermsOf lvl) x as' y bs'
        (SinglePlus (Plus k a) :| [] , _)
          | MetaV x as' <- ignoreBlocking a
          , Just b' <- subLevel k b -> meta x as' b'
        (_ , SinglePlus (Plus l b) :| [])
          | MetaV y bs' <- ignoreBlocking b
          , Just a' <- subLevel l a -> meta y bs' a'

        -- a' ⊔ b == b
        _ | Just a' <- levelMaxDiff a b
          , b /= ClosedLevel 0 -> leqLevel a' b

        -- a == b' ⊔ a
        _ | Just b' <- levelMaxDiff b a
          , a /= ClosedLevel 0 -> leqLevel b' a

        -- neutral/closed == neutral/closed
        (as , bs)
          | all isNeutralOrClosed (as <> bs)
          -- Andreas, 2013-10-31: There could be metas in neutral levels (see Issue 930).
          -- Should not we postpone there as well?  Yes!
          , not (any hasMeta (as <> bs))
          , length as == length bs -> do
              reportSLn "tc.conv.level" 60 $ "equalLevel: all are neutral or closed"
              List1.zipWithM_ ((===) `on` levelTm . unSingleLevel . fmap ignoreBlocking) as bs

        -- more cases?
        _ | noMetas (a , b) -> notok
          | otherwise       -> postpone

      where
        a === b = unlessM typeInType $ do
          lvl <- levelType'
          equalAtom (AsTermsOf lvl) a b

        -- perform assignment (MetaV x as) := b
        meta x as b = do
          reportSLn "tc.meta.level" 30 $ "Assigning meta level"
          reportSDoc "tc.meta.level" 50 $ "meta" <+> sep [prettyList $ map pretty as, pretty b]
          lvl <- levelType'
          assignE DirEq x as (levelTm b) (AsTermsOf lvl) (===) -- fallback: check equality as atoms

        isNeutral (SinglePlus (Plus _ NotBlocked{})) = True
        isNeutral _                                  = False

        isNeutralOrClosed (SingleClosed _)                   = True
        isNeutralOrClosed (SinglePlus (Plus _ NotBlocked{})) = True
        isNeutralOrClosed _                                  = False

        hasMeta (SinglePlus (Plus _ Blocked{})) = True
        hasMeta (SinglePlus (Plus _ a))         = isJust $ firstMeta $ ignoreBlocking a
        hasMeta (SingleClosed _)                = False

        removeSubsumed a b =
          let as = List1.toList $ levelMaxView a
              bs = List1.toList $ levelMaxView b
              a' = unSingleLevels $ filter (not . (`isStrictlySubsumedBy` bs)) as
              b' = unSingleLevels $ filter (not . (`isStrictlySubsumedBy` as)) bs
          in (a',b')

        x `isStrictlySubsumedBy` ys = any (`strictlySubsumes` x) ys

        SingleClosed m        `strictlySubsumes` SingleClosed n        = m > n
        SinglePlus (Plus m a) `strictlySubsumes` SingleClosed n        = m > n
        SinglePlus (Plus m a) `strictlySubsumes` SinglePlus (Plus n b) = a == b && m > n
        _                     `strictlySubsumes` _                     = False


{-# SPECIALIZE equalSort :: Sort -> Sort -> TCM () #-}
-- | Check that the first sort equal to the second.
equalSort :: forall m. MonadConversion m => Sort -> Sort -> m ()
equalSort s1 s2 = do
  reportSDoc "tc.conv.sort" 30 $ sep
    [ "equalSort"
    , vcat [ nest 2 $ fsep [ prettyTCM s1 <+> "=="
                           , prettyTCM s2 ]
           ]
    ]
  reportSDoc "tc.conv.sort" 60 $ sep
    [ "equalSort"
    , vcat [ nest 2 $ fsep [ pretty s1 <+> "=="
                           , pretty s2 ]
           ]
    ]
  whenProfile Profile.Conversion $ tick "compare sorts"

  guardPointerEquality s1 s2 "pointer equality: sorts" $
    SynEq.checkSyntacticEquality s1 s2 (\_ _ -> return ()) $ \s1 s2 -> do

    s1b <- reduceB s1
    s2b <- reduceB s2

    let (s1,s2) = (ignoreBlocking s1b, ignoreBlocking s2b)
        blocker = unblockOnEither (getBlocker s1b) (getBlocker s2b)

    let postponeIfBlocked = catchPatternErr $ \blocker -> do
          if | blocker == neverUnblock -> typeError $ UnequalSorts s1 s2
             | otherwise -> do
                 reportSDoc "tc.conv.sort" 30 $ vcat
                   [ "Postponing constraint"
                   , nest 2 $ fsep [ prettyTCM s1 <+> "=="
                                   , prettyTCM s2 ]
                   ]
                 -- Andreas, 2023-12-21, recomputing the blocker fixes issue #7034.
                 blocker <- updateBlocker blocker
                 addConstraint blocker $ SortCmp CmpEq s1 s2

    propEnabled <- isPropEnabled
    typeInTypeEnabled <- typeInType
    omegaInOmegaEnabled <- optOmegaInOmega <$> pragmaOptions
    let infInInf = typeInTypeEnabled || omegaInOmegaEnabled

    postponeIfBlocked $ case (s1, s2) of

            -- Andreas, 2018-09-03: crash on dummy sort
            (DummyS s, _) -> impossibleSort s
            (_, DummyS s) -> impossibleSort s

            -- one side is a meta sort: try to instantiate
            -- In case both sides are meta sorts, instantiate the
            -- bigger (i.e. more recent) one.
            (MetaS x es , MetaS y es') -> compareMetas CmpEq AsTypes x es y es'
            (MetaS x es , _          ) -> meta x es s2
            (_          , MetaS x es ) -> meta x es s1

            -- diagonal cases for rigid sorts
            (Univ u a   , Univ u' b  ) | u == u' -> equalLevel a b `catchInequalLevel` no
            (SizeUniv   , SizeUniv   ) -> yes
            (LockUniv   , LockUniv   ) -> yes
            (LevelUniv  , LevelUniv  ) -> yes
            (IntervalUniv , IntervalUniv) -> yes
            (Inf u m    , Inf u' n   ) ->
              if u == u' && (m == n || infInInf) then yes else no

            -- if --type-in-type is enabled, Setωᵢ is equal to any Set ℓ (see #3439)
            (Univ u _   , Inf  u' _  ) -> answer $ u == u' && typeInTypeEnabled
            (Inf  u _   , Univ u' _  ) -> answer $ u == u' && typeInTypeEnabled

            -- equating @PiSort a b@ to another sort
            (s1 , PiSort a b c) -> piSortEquals propEnabled s1 a b c blocker
            (PiSort a b c , s2) -> piSortEquals propEnabled s2 a b c blocker

            -- equating @FunSort a b@ to another sort
            (s1 , FunSort a b) -> funSortEquals propEnabled s1 a b blocker
            (FunSort a b , s2) -> funSortEquals propEnabled s2 a b blocker

            -- equating @UnivSort s@ to another sort
            (s1          , UnivSort s2) -> univSortEquals propEnabled infInInf s1 s2 blocker
            (UnivSort s1 , s2         ) -> univSortEquals propEnabled infInInf s2 s1 blocker

            -- postulated sorts can only be equal if they have the same head
            (DefS d es  , DefS d' es')
              | d == d'                -> do
                  pol <- getPolarity' CmpEq d
                  a <- computeElimHeadType d es es'
                  compareElims pol [] a (Def d []) es es'
              | otherwise              -> no

            -- any other combinations of sorts are not equal
            (_          , _          ) -> no

    where
      yes = return ()
      no  = patternViolation neverUnblock
      answer = \case
        True -> yes
        False -> no

      -- perform assignment (MetaS x es) := s
      meta :: MetaId -> [Elim' Term] -> Sort -> m ()
      meta x es s = do
        reportSLn "tc.meta.sort" 30 $ "Assigning meta sort"
        reportSDoc "tc.meta.sort" 50 $ "meta" <+> sep [pretty x, prettyList $ map pretty es, pretty s]
        assignE DirEq x es (Sort s) AsTypes __IMPOSSIBLE__

       -- Sorts that contain exactly one other kind of sorts.
      invertibleSort :: Bool -> Univ -> Bool
      invertibleSort propEnabled = \case
        -- @SSetω(n+1)@ is the successor sort of exactly @SSetω(n)@.
        USSet -> True
        -- @Setω(n+1)@ is the successor sort of exactly @Setω(n)@ if we do not have @Prop@.
        UType -> not propEnabled
        -- @Prop@ sorts are not successor sorts.
        UProp -> False

      -- Equate a sort @s1@ to @univSort s2@
      -- Precondition: @s1@ and @univSort s2@ are already reduced.
      univSortEquals :: Bool -> Bool -> Sort -> Sort -> Blocker -> m ()
      univSortEquals propEnabled infInInf s1 s2 blocker = do
        reportSDoc "tc.conv.sort" 35 $ vcat
          [ "univSortEquals"
          , "  s1 =" <+> prettyTCM s1
          , "  s2 =" <+> prettyTCM s2
          ]
        let postpone = patternViolation blocker
        case s1 of
          -- @Prop l@, @SizeUniv@ and @LevelUniv@ are not successor sorts.
          Prop{}      -> no
          Inf UProp _ -> no
          SizeUniv{}  -> no
          LevelUniv{} -> no
          -- Neither are @LockUniv@ or @IntervalUniv@.
          LockUniv{}     -> no
          IntervalUniv{} -> no

          -- @Set l1@ is the successor sort of either @Set l2@ or
          -- @Prop l2@ where @l1 == lsuc l2@.
          Type l1 -> do
            levelUnivEnabled <- optLevelUniverse <$> pragmaOptions
            guardedEnabled   <- optGuarded       <$> pragmaOptions
               -- @s2@ is definitely not @Inf n@ or @SizeUniv@
            if | Inf _ _n <- s2 -> __IMPOSSIBLE__
               | SizeUniv <- s2 -> __IMPOSSIBLE__
               -- The predecessor @s2@ is can also not be @SSet _@ or @IntervalUniv@
               | Univ USSet _ <- s2 -> __IMPOSSIBLE__
               | IntervalUniv <- s2 -> __IMPOSSIBLE__
               -- If @Prop@ is not used, then @s2@ must be of the form @Set l2@,
               -- except when l1 == 1, then it could also be @LockUniv@ or @LevelUniv@.
               | not (propEnabled || guardedEnabled || levelUnivEnabled) -> do
                   l2 <- case subLevel 1 l1 of
                     Just l2 -> return l2
                     Nothing -> do
                       l2 <- newLevelMeta
                       equalLevel l1 (levelSuc l2)
                       return l2
                   equalSort (Type l2) s2
               -- Otherwise we postpone
               | otherwise -> postpone
          -- @SSetω(n+1)@ is the successor sort of exactly @SSetω(n)@.
          -- @SSetω@ is the successor sort of exactly @SSetω@ if
          -- --type-in-type or --omega-in-omega is enabled.
          -- The same is only true for @Setω(n+1)@ if @Propω...@ are disabled.
          -- @Setω@ is the successor sort of @Setω@ (type:type) or @SizeUniv@ (--sized-types).
          Inf u 0 -> do
              -- Compute the predecessor(s) of (S)Setω and return it if it is unique.
              sizedTypesEnabled <- sizedTypesOption
              -- guardedEnabled <- optGuarded <$> pragmaOptions
              case concat
                [ [ s1       | u /= UProp, infInInf ]
                , [ dummy    | u == UType, infInInf, propEnabled, let dummy = Inf UProp 0 ]
                    -- We enter a dummy into the solution set if --prop makes predecessor ambiguous.
                , [ SizeUniv | u == UType, sizedTypesEnabled ]
                -- , [ LockUniv | guardedEnabled ]  -- LockUniv is actually in Set₁, not Setω
                ]
                of
                [ s ] -> equalSort s s2
                []    -> no
                _     -> postpone
          Inf u n | n > 0, invertibleSort propEnabled u ->
            equalSort (Inf u $ n - 1) s2

          -- Anything else: postpone
          _ -> postpone


      -- Equate a sort @s@ to @piSort a s1 s2@
      -- Precondition: @s@ and @piSort a s1 s2@ are already reduced.
      piSortEquals :: Bool -> Sort -> Dom Term -> Sort -> Abs Sort -> Blocker -> m ()
      piSortEquals propEnabled s a s1 NoAbs{} blocker = __IMPOSSIBLE__
      piSortEquals propEnabled s a s1 s2Abs@(Abs x s2) blocker = do
        let adom = El s1 <$> a
        reportSDoc "tc.conv.sort" 35 $ vcat
          [ "piSortEquals"
          , "  s  =" <+> prettyTCM s
          , "  a  =" <+> prettyTCM adom
          , "  s1 =" <+> prettyTCM s1
          , "  s2 =" <+> addContext (x,adom) (prettyTCM s2)
          ]
        let postpone = patternViolation blocker
           -- If @s2@ is dependent, then @piSort a s1 s2@ computes to
           -- @Setωi@. Hence, if @s@ is small, then @s2@
           -- cannot be dependent.
        if | isSmallSort s -> do
               -- We force @s2@ to be non-dependent by unifying it with
               -- a fresh meta that does not depend on @x : a@
               s2' <- newSortMeta
               addContext (x , adom) $ equalSort s2 (raise 1 s2')
               funSortEquals propEnabled s s1 s2' blocker
           -- Otherwise: postpone
           | otherwise -> postpone

      -- Equate a sort @s@ to @funSort s1 s2@
      -- Precondition: @s@ and @funSort s1 s2@ are already reduced
      funSortEquals :: Bool -> Sort -> Sort -> Sort -> Blocker -> m ()
      funSortEquals propEnabled s0 s1 s2 blocker = do
        reportSDoc "tc.conv.sort" 35 $ vcat
          [ "funSortEquals"
          , "  s0 =" <+> prettyTCM s0
          , "  s1 =" <+> prettyTCM s1
          , "  s2 =" <+> prettyTCM s2
          ]
        sizedTypesEnabled <- sizedTypesOption
        cubicalEnabled <- isJust <$> cubicalOption
        levelUnivEnabled <- optLevelUniverse <$> pragmaOptions
        let postpone = patternViolation blocker
            err :: m ()
            err = typeError $ UnequalSorts s0 (FunSort s1 s2)
        case s0 of
          -- If @Setωᵢ == funSort s1 s2@, then either @s1@ or @s2@ must
          -- be @Setωᵢ@.

          Inf u n ->
            case (sizeOfSort s1, sizeOfSort s2) of

              -- Both sorts have to be <= n in size, and their fibrancy <= u
              (Right (SizeOfSort u' n'), _)
                | n' > n                           -> err
                | univFibrancy u' > univFibrancy u -> err
              (_, Right (SizeOfSort u' n'))
                | n' > n                           -> err
                | univFibrancy u' > univFibrancy u -> err
              -- Unless SSet, the kind of the funSort is the kind of the codomain
                | u /= USSet, u /= u'              -> err

              -- One sort has to be at least the same size as n
              (Right (SizeOfSort u1 n1), Right (SizeOfSort u2 n2))
                | n1 < n, n2 < n                   -> err
                | u /= funUniv u1 u2               -> err

              -- If have the domain sort only
              (Right (SizeOfSort u' n'), _)
                | u' /= USSet, n' < n              -> equalSort s0 s2
                | otherwise                        -> postpone

              -- If we just have the codomain sort
              (_, Right (SizeOfSort USSet n'))     -> postpone
              (_, Right (SizeOfSort _     n'))
                | n' < n, u == USSet               -> equalSort s1 s2
                | n' < n, not propEnabled,
                  -- issue #6648: with --level-universe we have PTS rule (LevelUniv,Set,Setω)
                  not levelUnivEnabled || n > 0    -> equalSort (Inf UType n) s1
                | otherwise                        -> postpone

              _ -> postpone

          -- If @Set l == funSort s1 s2@, then @s2@ must be of the
          -- form @Set l2@. @s1@ can be one of @Set l1@, @Prop l1@,
          -- @SizeUniv@, or @IUniv@.
          Type l -> do
            l2 <- forceUniv UType s2
            -- We must have @l2 =< l@, this might help us to solve
            -- more constraints (in particular when @l == 0@).
            leqLevel l2 l
            -- Jesper, 2022-10-22, #6211: the operations `forceUniv`
            -- and `leqLevel` above might have instantiated some
            -- metas, so we need to reduce s1 again to get an
            -- up-to-date Blocker.
            s1b <- reduceB s1
            let s1 = ignoreBlocking s1b
                blocker = getBlocker s1b
            -- Jesper, 2019-12-27: SizeUniv is disabled at the moment.
            if | {- sizedTypesEnabled || -} propEnabled || cubicalEnabled ->
                case funSort' s1 (Type l2) of
                   -- If the work we did makes the @funSort@ compute,
                   -- continue working.
                   Right s -> equalSort (Type l) s
                   -- Otherwise: postpone
                   Left{}  -> patternViolation blocker
               -- If both Prop and sized types are disabled, only the
               -- case @s1 == Set l1@ remains.
               | otherwise -> do
                   l1 <- forceUniv UType s1
                   equalLevel l (levelLub l1 l2)

          -- If @Prop l == funSort s1 s2@, then @s2@ must be of the
          -- form @Prop l2@, and @s1@ can be one of @Set l1@, Prop
          -- l1@, or @SizeUniv@.
          Prop l -> do
            l2 <- forceUniv UProp s2
            leqLevel l2 l
            s1b <- reduceB s1
            let s1 = ignoreBlocking s1b
                blocker = getBlocker s1b
            case funSort' s1 (Prop l2) of
                   -- If the work we did makes the @funSort@ compute,
                   -- continue working.
                   Right s -> equalSort (Prop l) s
                   -- Otherwise: postpone
                   Left _  -> patternViolation blocker

          -- TODO: SSet l

          -- We have @SizeUniv == funSort s1 s2@ iff @s2 == SizeUniv@
          SizeUniv -> equalSort SizeUniv s2
          LevelUniv -> equalSort LevelUniv s2
          -- Anything else: postpone
          _        -> postpone

      forceUniv :: Univ -> Sort -> m Level
      forceUniv u = \case
        Univ u' l | u == u' -> return l
        s -> do
          l <- newLevelMeta
          equalSort s (Univ u l)
          return l

      impossibleSort s = do
        reportS "impossible" 10
          [ "equalSort: found dummy sort with description:"
          , s
          ]
        __IMPOSSIBLE__

      catchInequalLevel m fail = m `catchError` \case
        TypeError{} -> fail
        err         -> throwError err


forallFaceMaps
  :: MonadConversion m
  => Term
  -> (IntMap Bool -> Blocker -> Term -> m a)
  -> (IntMap Bool -> Substitution -> m a)
  -> m [a]
forallFaceMaps t kb k = do
  reportSDoc "conv.forall" 20 $
      fsep ["forallFaceMaps"
           , prettyTCM t
           ]
  as <- decomposeInterval t
  boolToI <- do
    io <- primIOne
    iz <- primIZero
    return (\b -> if b then io else iz)
  forM as $ \ (ms,ts) -> do
   ifBlockeds ts (kb ms) $ \ _ _ -> do
    let xs = map (second boolToI) $ IntMap.toAscList ms
    cxt <- getContext
    reportSDoc "conv.forall" 20 $
      fsep ["substContextN"
           , prettyTCM cxt
           , prettyTCM xs
           ]
    (cxt',sigma) <- substContextN cxt xs
    resolved <- forM xs (\ (i,t) -> (,) <$> lookupBV i <*> return (applySubst sigma t))
    updateContext sigma (const cxt') $
      addBindings resolved $ do
        cl <- buildClosure ()
        tel <- getContextTelescope
        m <- currentModule
        sub <- getModuleParameterSub m
        reportSDoc "conv.forall" 30 $ vcat
          [ text (replicate 10 '-')
          , prettyTCM (envCurrentModule $ clEnv cl)
          -- , prettyTCM (envLetBindings $ clEnv cl)
          , prettyTCM tel -- (toTelescope $ envContext $ clEnv cl)
          , prettyTCM sigma
          , prettyTCM m
          , prettyTCM sub
          ]
        k ms sigma
  where
    -- TODO Andrea: inefficient because we try to reduce the ts which we know are in whnf
    ifBlockeds ts blocked unblocked = do
      and <- getPrimitiveTerm PrimIMin
      io  <- primIOne
      let t = foldr (\ x r -> and `apply` [argN x,argN r]) io ts
      ifBlocked t blocked unblocked
    addBindings [] m = m
    addBindings ((Dom{domInfo = info,unDom = (nm,ty)},t):bs) m = addLetBinding info Inserted nm t ty (addBindings bs m)

    substContextN :: MonadConversion m => Context -> [(Int,Term)] -> m (Context , Substitution)
    substContextN c [] = return (c, idS)
    substContextN c ((i,t):xs) = do
      (c', sigma) <- substContext i t c
      (c'', sigma')  <- substContextN c' (map (subtract 1 -*- applySubst sigma) xs)
      return (c'', applySubst sigma' sigma)


    -- assumes the term can be typed in the shorter telescope
    -- the terms we get from toFaceMaps are closed.
    substContext :: MonadConversion m => Int -> Term -> Context -> m (Context , Substitution)
    substContext i t [] = __IMPOSSIBLE__
    substContext i t (x:xs) | i == 0 = return $ (xs , singletonS 0 t)
    substContext i t (x:xs) | i > 0 = do
                                  reportSDoc "conv.forall" 20 $
                                    fsep ["substContext"
                                        , text (show (i-1))
                                        , prettyTCM t
                                        , prettyTCM xs
                                        ]
                                  (c,sigma) <- substContext (i-1) t xs
                                  let e = applySubst sigma x
                                  return (e:c, liftS 1 sigma)
    substContext i t (x:xs) = __IMPOSSIBLE__

compareInterval :: MonadConversion m => Comparison -> Type -> Term -> Term -> m ()
compareInterval cmp i t u = do
  reportSDoc "tc.conv.interval" 15 $
    sep [ "{ compareInterval" <+> prettyTCM t <+> "=" <+> prettyTCM u ]
  whenProfile Profile.Conversion $ tick "compare at interval type"
  tb <- reduceB t
  ub <- reduceB u
  let t = ignoreBlocking tb
      u = ignoreBlocking ub
  it <- decomposeInterval' t
  iu <- decomposeInterval' u
  case () of
    _ | isBlocked tb || isBlocked ub -> do
      -- in case of metas we wouldn't be able to make progress by how we deal with de morgan laws.
      -- (because the constraints generated by decomposition are sufficient but not necessary).
      -- but we could still prune/solve some metas by comparing the terms as atoms.
      -- also if blocked we won't find the terms conclusively unequal(?) so compareAtom
      -- won't report type errors when we should accept.
      interval <- primIntervalType
      compareAtom CmpEq (AsTermsOf interval) t u
    _ | otherwise -> do
      x <- leqInterval it iu
      y <- leqInterval iu it
      let final = isCanonical it && isCanonical iu
      if x && y then reportSDoc "tc.conv.interval" 15 $ "Ok! }" else
        if final then typeError $ UnequalTerms cmp t u (AsTermsOf i)
                 else do
                   reportSDoc "tc.conv.interval" 15 $ "Giving up! }"
                   patternViolation (unblockOnAnyMetaIn (t, u))
 where
   isBlocked Blocked{}    = True
   isBlocked NotBlocked{} = False


type Conj = (IntMap BoolSet, [Term])

isCanonical :: [Conj] -> Bool
isCanonical = all (null . snd)

-- | leqInterval r q = r ≤ q in the I lattice.
-- (∨ r_i) ≤ (∨ q_j)  iff  ∀ i. ∃ j. r_i ≤ q_j
leqInterval :: MonadConversion m => [Conj] -> [Conj] -> m Bool
leqInterval r q =
  and <$> forM r (\ r_i ->
   or <$> forM q (\ q_j -> leqConj r_i q_j))  -- TODO shortcut

-- | leqConj r q = r ≤ q in the I lattice, when r and q are conjuctions.
-- ' (∧ r_i)   ≤ (∧ q_j)               iff
-- ' (∧ r_i)   ∧ (∧ q_j)   = (∧ r_i)   iff
-- ' {r_i | i} ∪ {q_j | j} = {r_i | i} iff
-- ' {q_j | j} ⊆ {r_i | i}
leqConj :: MonadConversion m => Conj -> Conj -> m Bool
leqConj (rs, rst) (qs, qst) = do
  if IntMap.isSubmapOfBy BoolSet.isSubsetOf qs rs
    then do
      interval <-
        El IntervalUniv . fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinInterval
      -- we don't want to generate new constraints here because
      -- 1. in some situations the same constraint would get generated twice.
      -- 2. unless things are completely accepted we are going to
      --    throw patternViolation in compareInterval.
      let eqT t u = tryConversion (compareAtom CmpEq (AsTermsOf interval) t u)
      let listSubset ts us =
            and <$> forM ts (\t -> or <$> forM us (\u -> eqT t u)) -- TODO shortcut
      listSubset qst rst
    else
      return False

-- | equalTermOnFace φ A u v = _ , φ ⊢ u = v : A
equalTermOnFace :: MonadConversion m => Term -> Type -> Term -> Term -> m ()
equalTermOnFace = compareTermOnFace CmpEq

compareTermOnFace :: MonadConversion m => Comparison -> Term -> Type -> Term -> Term -> m ()
compareTermOnFace = compareTermOnFace' (const compareTerm)

compareTermOnFace'
  :: MonadConversion m
  => (Substitution -> Comparison -> Type -> Term -> Term -> m ())
  -> Comparison -> Term -> Type -> Term -> Term -> m ()
compareTermOnFace' k cmp phi ty u v = do
  reportSDoc "tc.conv.face" 40 $
    text "compareTermOnFace:" <+> pretty phi <+> "|-" <+> pretty u <+> "==" <+> pretty v <+> ":" <+> pretty ty
  whenProfile Profile.Conversion $ tick "compare at face type"

  phi <- reduce phi
  _ <- forallFaceMaps phi postponed $ \ faces alpha ->
      k alpha cmp (applySubst alpha ty) (applySubst alpha u) (applySubst alpha v)
  return ()
 where
  postponed ms blocker psi = do
    phi <- runNamesT [] $ do
             imin <- cl $ getPrimitiveTerm PrimIMin
             ineg <- cl $ getPrimitiveTerm PrimINeg
             psi <- open psi
             let phi = foldr (\ (i,b) r -> do i <- open (var i); pure imin <@> (if b then i else pure ineg <@> i) <@> r)
                          psi (IntMap.toList ms) -- TODO Andrea: make a view?
             phi
    addConstraint blocker (ValueCmpOnFace cmp phi ty u v)

---------------------------------------------------------------------------
-- * Definitions
---------------------------------------------------------------------------

bothAbsurd :: MonadConversion m => QName -> QName -> m Bool
bothAbsurd f f'
  | isAbsurdLambdaName f, isAbsurdLambdaName f' = do
      -- Double check we are really dealing with absurd lambdas:
      -- Their functions should not have bodies.
      def  <- getConstInfo f
      def' <- getConstInfo f'
      case (theDef def, theDef def') of
        (Function{ funClauses = [Clause{ clauseBody = Nothing }] },
         Function{ funClauses = [Clause{ clauseBody = Nothing }] }) -> return True
        _ -> return False
  | otherwise = return False

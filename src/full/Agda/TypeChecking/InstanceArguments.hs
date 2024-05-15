{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.InstanceArguments
  ( findInstance
  , isInstanceConstraint
  , solveAwakeInstanceConstraints
  , shouldPostponeInstanceSearch
  , postponeInstanceConstraints
  , getInstanceCandidates
  , getInstanceDefs
  , OutputTypeName(..)
  , getOutputTypeName
  , addTypedInstance
  , addTypedInstance'
  , pruneTemporaryInstances
  , resolveInstanceHead
  ) where

import Control.Monad          (forM, filterM)
import Control.Monad.Except   (ExceptT(..), runExceptT, MonadError(..))
import Control.Monad.Trans    (lift )
-- import Control.Monad.IO.Class (liftIO)

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.List as List
import Data.Function (on)
import Data.Monoid hiding ((<>))
import Data.Foldable (toList, foldrM)

import Agda.Interaction.Options (optQualifiedInstances)

import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name (isQualified)
import Agda.Syntax.Position
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.MetaVars
import Agda.Syntax.Scope.Base (isNameInScope, inverseScopeLookupName', AllowAmbiguousNames(..))

import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Conversion.Pure (pureEqualTerm)
import Agda.TypeChecking.Errors () --instance only
import Agda.TypeChecking.Implicit (implicitArgs)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Records
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Warnings
import Agda.TypeChecking.Datatypes

import {-# SOURCE #-} Agda.TypeChecking.Constraints
import {-# SOURCE #-} Agda.TypeChecking.Conversion

import qualified Agda.Benchmarking as Benchmark
import Agda.TypeChecking.Monad.Benchmark (billTo)

import Agda.Utils.Lens
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Tuple
import Agda.Syntax.Common.Pretty (prettyShow)

import qualified Agda.Utils.ProfileOptions as Profile
-- import qualified Agda.Utils.HashTable as HashTable
import Agda.Utils.Impossible
-- import Agda.Utils.HashTable (HashTable)

import Agda.TypeChecking.DiscrimTree
-- import GHC.IO (unsafePerformIO)

-- | Compute a list of instance candidates.
--   'Nothing' if target type or any context type is a meta, error if
--   type is not eligible for instance search.
initialInstanceCandidates :: Bool -> Type -> TCM (Either Blocker [Candidate])
initialInstanceCandidates blockOverlap instTy = do
  (_, _, otn) <- getOutputTypeName instTy
  case otn of
    NoOutputTypeName -> typeError $ GenericError $
      "Instance search can only be used to find elements in a named type"
    OutputTypeNameNotYetKnown b -> do
      reportSDoc "tc.instance.cands" 30 $ "Instance type is not yet known. "
      return (Left b)
    OutputTypeVisiblePi -> typeError $ GenericError $
      "Instance search cannot be used to find elements in an explicit function type"
    OutputTypeVar -> do
      reportSDoc "tc.instance.cands" 30 $ "Instance type is a variable. "
      runBlocked (getContextCands Nothing)
    OutputTypeName n -> Bench.billTo [Bench.Typing, Bench.InstanceSearch, Bench.InitialCandidates] do
      reportSDoc "tc.instance.cands" 30 $ "Found instance type head: " <+> prettyTCM n
      runBlocked do
        local  <- getContextCands (Just n)
        global <- getScopeDefs n
        lift $ tickCandidates n $ length local + length global
        pure $ local <> global
  where
    -- Ticky profiling for statistics about a class.
    tickCandidates n size = whenProfile Profile.Instances do
      n <- prettyTCM n
      let pref = "class " <> show n

      -- Number of instance constraints of this class that have gotten a
      -- set of candidates
      tick $ pref <> ": attempts"
      -- Per-class info: number of constraints where there was only one
      -- candidate (awesome) + the total number of candidates we've gone
      -- through.
      when (size == 1) $ tick $ pref <> ": only one candidate"
      when (size >= 1) $ tickN
        (pref <> ": total candidates visited")
        (fromIntegral size)

    -- get a list of variables with their type, relative to current context
    getContextCands :: Maybe QName -> BlockT TCM [Candidate]
    getContextCands cls = do
      ctx <- getContext
      reportSDoc "tc.instance.cands" 40 $ hang "Getting candidates from context" 2 (inTopContext $ prettyTCM $ PrettyContext ctx)
          -- Context variables with their types lifted to live in the full context
      let varsAndRaisedTypes = reverse $ zip (contextTerms ctx) (flattenTel $ contextToTel ctx)
          vars = [ Candidate LocalCandidate x t (infoOverlapMode info)
                 | (x, Dom{domInfo = info, unDom = t}) <- varsAndRaisedTypes
                 , isInstance info
                 ]

      -- {{}}-fields of variables are also candidates
      let cxtAndTypes = [ (LocalCandidate, x, t) | (x, Dom{unDom = t}) <- varsAndRaisedTypes ]
      fields <- concat <$> mapM instanceFields (reverse cxtAndTypes)
      reportSDoc "tc.instance.fields" 30 $
        if null fields then "no instance field candidates" else
          "instance field candidates" $$ do
            nest 2 $ vcat (map debugCandidate fields)

      -- get let bindings
      env <- asksTC envLetBindings
      env <- mapM (traverse getOpen) $ Map.toList env
      let lets = [ Candidate LocalCandidate v t DefaultOverlap
                 | (_, LetBinding _ v Dom{domInfo = info, unDom = t}) <- env
                 , isInstance info
                 , usableModality info
                 ]
      filterM (sameHead cls . candidateType) $ vars ++ fields ++ lets

    sameHead :: Maybe QName -> Type -> BlockT TCM Bool
    sameHead Nothing _ = pure True
    sameHead (Just cls) t = lift (thd3 <$> getOutputTypeName t) >>= \case
      OutputTypeName            inst -> pure (inst == cls)
      OutputTypeNameNotYetKnown b    -> patternViolation b
      _                              -> pure False

    infoOverlapMode :: LensArgInfo a => a -> OverlapMode
    infoOverlapMode info = if isYesOverlap (getArgInfo info) then FieldOverlap else DefaultOverlap

    etaExpand :: (MonadTCM m, PureTCM m)
              => Bool -> Type -> m (Maybe (QName, Args))
    etaExpand etaOnce t =
      isEtaRecordType t >>= \case
        Nothing | etaOnce -> do
          isRecordType t >>= \case
            Nothing         -> return Nothing
            Just (r, vs, _) -> do
              m <- currentModule
              -- Are we inside the record module? If so it's safe and desirable
              -- to eta-expand once (issue #2320).
              if qnameToList0 r `List.isPrefixOf` mnameToList m
                then return (Just (r, vs))
                else return Nothing
        r -> return r

    instanceFields :: (CandidateKind,Term,Type) -> BlockT TCM [Candidate]
    instanceFields = instanceFields' True

    instanceFields' :: Bool -> (CandidateKind,Term,Type) -> BlockT TCM [Candidate]
    instanceFields' etaOnce (q, v, t) =
      ifBlocked t (\ m _ -> patternViolation m) $ \ _ t -> do
      caseMaybeM (etaExpand etaOnce t) (return []) $ \ (r, pars) -> do
        (tel, args) <- lift $ forceEtaExpandRecord r pars v
        let types = map unDom $ applySubst (parallelS $ reverse $ map unArg args) (flattenTel tel)
        fmap concat $ forM (zip args types) $ \ (arg, t) ->
          ([ Candidate LocalCandidate (unArg arg) t (infoOverlapMode arg)
           | isInstance arg
           ] ++) <$>
          instanceFields' False (LocalCandidate, unArg arg, t)

    getScopeDefs :: QName -> BlockT TCM [Candidate]
    getScopeDefs n = do
      rel <- viewTC eRelevance

      InstanceTable tree counts <- lift getInstanceDefs
      QueryResult qs blocker <- lift $ lookupDT (unEl instTy) tree

      mutual <- caseMaybeM (asksTC envMutualBlock) (pure mempty) \mb ->
        mutualNames <$> lookupMutualBlock mb

      reportSDoc "tc.instance.candidates.search" 20 $ vcat
        [ "instance candidates from signature for goal:"
        , nest 2 (prettyTCM =<< instantiateFull instTy)
        , nest 2 (prettyTCM qs) <+> "length:" <+> prettyTCM (length qs)
        , "blocker:"
        , nest 2 (prettyTCM blocker)
        , "mutual block:"
        , nest 2 (prettyTCM mutual)
        ]

      cands <- catMaybes <$> mapM (lift . candidate rel) (toList qs)

      recursive <- useTC stConsideringInstance
      prefreeze <- useTC stMutualChecks

      let
        -- When possible, we block the instance selection process early
        -- and accurately when there is some overlap. "When possible"
        -- turns out to be a bit hairy:
        block = and
          [ not (Set.null (allBlockingMetas blocker))
            -- If we're not blocked on any metas, we might as well check
            -- all the candidates to see if the overlap was resolvable.
            -- Keep going.

          , length cands > 1
            -- If there's no overlap, blocking might be counterproductive.

          , Set.disjoint mutual qs
            -- The results of termination checking depends on whether we
            -- solve instance metas eagerly or late. Consider
            --
            --   instance Show-List = record { show = go }
            --   go (x ∷ xs) = show x <> show ⦃ ?0 ⦄ xs
            --
            -- If we solve ?0 eagerly, the term we use is the literal
            -- record constructor. The 'show' projection unfolds in 'go'
            -- and the termination check is happy.
            --
            -- If we solve it late, we run the risk of the clause
            -- compiler applying copattern translation to Show-List. The
            -- 'show' projection does not eagerly unfold, and the
            -- termination check explodes.

          , not recursive
            -- Blocking instance selection *on a meta* while considering
            -- an instance causes the recursive instance constraint to
            -- get repeatedly woken up. Not good for performance.

          , not prefreeze
            -- During the pre-freeze wakeupConstraints_, we don't
            -- eagerly block on overlap. This is because we might have a
            -- pair of constraints
            --
            --   instance ?1 : Foo ?0, blocked on ?0, candidates Foo T, Foo S
            --   ?0 = T (blocked on ?0)
            --
            -- If we block ?1 on ?0, then this pair goes unsolved --- ?0
            -- gets frozen and there's no way for us to make any more
            -- progress. But if we let the overlapping candidates
            -- through, checkCandidateForMeta will wake up the ?0 = T
            -- constraint in each case, which rules out the 'Foo S'
            -- candidate: both constraints get solved.

          , blockOverlap
            -- For the getInstances reflection primitive, we don't want
            -- to block on overlap, so that the user can do their thing.
          ]

      when block do
        reportSDoc "tc.instance.candidates.search" 20 $
          "postponing because of overlap:" <+> prettyTCM blocker
        patternViolation blocker

      -- Some more class-specific profiling.
      lift $ whenProfile Profile.Instances case Map.lookup n counts of
        Just tot -> do
          n <- prettyTCM n
          -- Record the overall total number of candidates that were
          -- skipped by lookup in the discrimination tree, and record
          -- this per-class, as well.
          let diff = fromIntegral (tot - length cands)
          tickN "instances discarded early" diff
          tickN ("class " <> show n <> ": discarded early") diff
        Nothing  -> pure ()

      pure cands

    candidate :: Relevance -> QName -> TCM (Maybe Candidate)
    candidate rel q = ifNotM (isNameInScope q <$> getScope) (return Nothing) $ do
      -- Jesper, 2020-03-16: When using --no-qualified-instances,
      -- filter out instances that are only in scope under a qualified
      -- name.
      filterQualified $ do
      -- Andreas, 2012-07-07:
      -- we try to get the info for q
      -- while opening a module, q may be in scope but not in the signature
      -- in this case, we just ignore q (issue 674)
      flip catchError handle $ do
        def <- getConstInfo q
        if not (getRelevance def `moreRelevant` rel) then return Nothing else do
          -- Andreas, 2017-01-14: instantiateDef is a bit of an overkill
          -- if we anyway get the freeVarsToApply
          -- WAS: t <- defType <$> instantiateDef def
          args <- freeVarsToApply q
          let
            t   = defType def `piApply` args
            rel = getRelevance $ defArgInfo def

            v = case theDef def of
              -- drop parameters if it's a projection function...
              Function{ funProjection = Right p } -> projDropParsApply p ProjSystem rel args

              -- Andreas, 2014-08-19: constructors cannot be declared as
              -- instances (at least as of now).
              -- I do not understand why the Constructor case is not impossible.
              -- Ulf, 2014-08-20: constructors are always instances.
              Constructor{ conSrcCon = c }       -> Con c ConOSystem []
              _                                  -> Def q $ map Apply args

            mode = case defInstance def of
              Just i  -> instanceOverlap i
              Nothing -> DefaultOverlap

          return $ Just $ Candidate (GlobalCandidate q) v t mode
      where
        -- unbound constant throws an internal error
        handle (TypeError _ _ (Closure {clValue = InternalError _})) = return Nothing
        handle err                                                   = throwError err

        filterQualified :: TCM (Maybe Candidate) -> TCM (Maybe Candidate)
        filterQualified m = ifM (optQualifiedInstances <$> pragmaOptions) m $ do
          qc <- inverseScopeLookupName' AmbiguousAnything q <$> getScope
          let isQual = maybe True isQualified $ listToMaybe qc
          reportSDoc "tc.instance.qualified" 30 $
            if isQual then
              "dropping qualified instance" <+> prettyTCM q
            else
              "keeping instance" <+> prettyTCM q <+>
              "since it is in scope as" <+> prettyTCM qc
          if isQual then return Nothing else m


-- | @findInstance m (v,a)s@ tries to instantiate on of the types @a@s
--   of the candidate terms @v@s to the type @t@ of the metavariable @m@.
--   If successful, meta @m@ is solved with the instantiation of @v@.
--   If unsuccessful, the constraint is regenerated, with possibly reduced
--   candidate set.
--   The list of candidates is equal to @Nothing@ when the type of the meta
--   wasn't known when the constraint was generated. In that case, try to find
--   its type again.
findInstance :: MetaId -> Maybe [Candidate] -> TCM ()
findInstance m Nothing = do
  ifM canDropRecursiveInstance (addConstraint neverUnblock (FindInstance m Nothing)) do
  -- Andreas, 2015-02-07: New metas should be created with range of the
  -- current instance meta, thus, we set the range.
  mv <- lookupLocalMeta m
  setCurrentRange mv $ do
    reportSLn "tc.instance" 20 $ "The type of the FindInstance constraint isn't known, trying to find it again."
    t <- instantiate =<< getMetaTypeInContext m
    reportSLn "tc.instance" 70 $ "findInstance 1: t: " ++ prettyShow t

    -- Issue #2577: If the target is a function type the arguments are
    -- potential candidates, so we add them to the context to make
    -- initialInstanceCandidates pick them up.
    TelV tel t <- telViewUpTo' (-1) notVisible t
    cands <- addContext tel $ initialInstanceCandidates True t
    case cands of
      Left unblock -> do
        reportSLn "tc.instance" 20 "Can't figure out target of instance goal. Postponing constraint."
        addConstraint unblock $ FindInstance m Nothing
      Right cs -> findInstance m (Just cs)

findInstance m (Just cands) =                          -- Note: if no blocking meta variable this will not unblock until the end of the mutual block
  whenJustM (findInstance' m cands) $ (\ (cands, b) -> addConstraint b $ FindInstance m $ Just cands)

-- | Entry point for `tcGetInstances` primitive
getInstanceCandidates :: MetaId -> TCM (Either Blocker [Candidate])
getInstanceCandidates m = wrapper where
  wrapper = do
    mv <- lookupLocalMeta m
    setCurrentRange mv $ do
      t <- instantiate =<< getMetaTypeInContext m
      TelV tel t' <- telViewUpTo' (-1) notVisible t
      addContext tel $ runExceptT (worker t')

  insertCandidate :: Candidate -> [Candidate] -> TCM [Candidate]
  insertCandidate x []     = pure [x]
  insertCandidate x (y:xs) = doesCandidateSpecialise x y >>= \case
    True  -> pure (x:y:xs)
    False -> (y:) <$> insertCandidate x xs

  worker :: Type -> ExceptT Blocker TCM [Candidate]
  worker t' = do
    cands <- ExceptT (initialInstanceCandidates False t')
    cands <- lift (checkCandidates m t' cands) <&> \case
      Nothing         -> cands
      Just (_, cands) -> fst <$> cands
    cands <- Bench.billTo [Bench.Typing, Bench.InstanceSearch, Bench.OrderCandidates] $
      lift (foldrM insertCandidate [] cands)

    reportSDoc "tc.instance.sort" 20 $ nest 2 $
      "sorted candidates" $$ vcat (map debugCandidate cands)

    pure cands

-- | @'doesCandidateSpecialise' c1 c2@ checks whether the instance
-- candidate @c1@ /specialises/ the instance candidate @c2@, i.e.,
-- whether the type of @c2@ is a substitution instance of @c1@'s type.
--
-- Only the final return type of the instances is considered: the
-- presence of unsolvable instance arguments in the types of @c1@ or
-- @c2@ does not affect the results of 'doesCandidateSpecialise'.
doesCandidateSpecialise :: Candidate -> Candidate -> TCM Bool
doesCandidateSpecialise c1@Candidate{candidateType = t1} c2@Candidate{candidateType = t2} = do
  whenProfile Profile.Instances $ tick "doesCandidateSpecialise"

  -- We compare
  --    c1 : ∀ {Γ} → T
  -- against
  --    c2 : ∀ {Δ} → S
  -- by moving to the context Γ ⊢, so that any variables in T's type are
  -- "rigid", but *instantiating* S[?/Δ], so its variables are
  -- "flexible"; then calling the conversion checker.

  let
    handle e = do
      reportSDoc "tc.instance.sort" 30 $ nest 2 "=> NOT specialisation"
      reportSDoc "tc.instance.sort" 40 $ prettyTCM e
      pure False

    wrap = flip catchError handle
        -- Turn failures into returning false
        . localTCState
        -- Discard any changes to the TC state (metas from
        -- instantiating t2, recursive instance constraints, etc)
        . locallyTCState stPostponeInstanceSearch (const True)
        -- Don't spend any time looking for instances in the contexts
        . nowConsideringInstance
        -- Don't execute tactics either

  TelV tel t1 <- telView t1
  addContext tel $ wrap $ do
    (args, t2) <- implicitArgs (-1) (\h -> notVisible h) t2

    reportSDoc "tc.instance.sort" 30 $ "Does" <+> prettyTCM (raise (length tel) c1) <+> "specialise" <+> (prettyTCM (raise (length tel) c2) <> "?")
    reportSDoc "tc.instance.sort" 60 $ vcat
      [ "Comparing candidate"
      , nest 2 (prettyTCM c1 <+> colon <+> prettyTCM t1)
      , "vs"
      , nest 2 (prettyTCM c2 <+> colon <+> prettyTCM t2)
      ]

    leqType t2 t1
    reportSDoc "tc.instance.sort" 30 $ nest 2 "=> IS specialisation"
    pure True

-- | Checks whether an instance overlaps another. This involves a strict
-- specificity check (the new instance should be more specific than the
-- old instance but not vice-versa) and the consideration of whether
-- these instances are overlappable/overlapping at all.
--
-- Fails early if the new candidate is not overlapping and the old
-- candidate is not overlappable.
doesCandidateOverlap :: Candidate -> Candidate -> TCM Bool
doesCandidateOverlap new old = if isOverlapping new || isOverlappable old
  then andM [ doesCandidateSpecialise new old
            , fmap not (doesCandidateSpecialise old new) ]
  else pure False

-- | Result says whether we need to add constraint, and if so, the set of
--   remaining candidates and an eventual blocking metavariable.
findInstance' :: MetaId -> [Candidate] -> TCM (Maybe ([Candidate], Blocker))
findInstance' m cands = do
  let
    frozen = do
      reportSLn "tc.instance.defer" 20 "Refusing to solve frozen instance meta."
      whenProfile Profile.Instances $ tick "findInstance: frozen"
      return (Just (cands, neverUnblock))

    recursive = do
      recur <- useTC stConsideringInstance
      reportSLn "tc.instance.defer" 20
        if recur
          then "Postponing recursive instance search."
          else "Postponing possibly recursive instance search."
      whenProfile Profile.Instances $ tick "findInstance: recursive"
      return $ Just (cands, neverUnblock)

  ifM (isFrozen m) frozen do
  ifM shouldPostponeInstanceSearch recursive do
  billTo [Benchmark.Typing, Benchmark.InstanceSearch] do

  -- Andreas, 2015-02-07: New metas should be created with range of the
  -- current instance meta, thus, we set the range.
  mv <- lookupLocalMeta m
  setCurrentRange mv $ do
      reportSLn "tc.instance" 15 $
        "findInstance 2: constraint: " ++ prettyShow m ++ "; candidates left: " ++ show (length cands)
      reportSDoc "tc.instance" 60 $ nest 2 $ vcat $ map debugCandidate cands
      reportSDoc "tc.instance" 70 $ "raw" $$ do
       nest 2 $ vcat $ map debugCandidateRaw cands

      t <- getMetaTypeInContext m
      reportSLn "tc.instance" 70 $ "findInstance 2: t: " ++ prettyShow t

      insidePi t $ \ t -> do
      reportSDoc "tc.instance" 15 $ "findInstance 3: t =" <+> prettyTCM t
      reportSLn "tc.instance" 70 $ "findInstance 3: t: " ++ prettyShow t

      mcands <-
        -- Temporarily remove other instance constraints to avoid
        -- redundant solution attempts
        holdConstraints (const isInstanceProblemConstraint) $
        checkCandidates m t cands

      debugConstraints
      case mcands of
        Just ([(_, err)], []) -> do
          reportSDoc "tc.instance" 15 $
            "findInstance 5: the only viable candidate failed..."
          throwError err

        Just (errs, []) -> do
          if null errs then reportSDoc "tc.instance" 15 $ "findInstance 5: no viable candidate found..."
                       else reportSDoc "tc.instance" 15 $ "findInstance 5: all viable candidates failed..."
          -- #3676: Sort the candidates based on the size of the range for the errors and
          --        set the range of the full error to the range of the most precise candidate
          --        error.
          let sortedErrs = List.sortBy (compare `on` precision) errs
                where precision (_, err) = maybe infinity iLength $ rangeToInterval $ getRange err
                      infinity = 1000000000
          setCurrentRange (take 1 $ map snd sortedErrs) $
            typeError $ InstanceNoCandidate t [ (candidateTerm c, err) | (c, err) <- sortedErrs ]

        Just (errs, [(c@(Candidate q term t' _), v)]) -> do
          reportSDoc "tc.instance" 15 $ vcat
            [ "instance search: attempting"
            , nest 2 $ prettyTCM m <+> ":=" <+> prettyTCM v
            ]

          reportSDoc "tc.instance" 70 $ nest 2 $
            "candidate v = " <+> pretty v

          ctxElims <- map Apply <$> getContextArgs
          equalTerm t (MetaV m ctxElims) v

          reportSDoc "tc.instance" 15 $ vcat
            [ "findInstance 5: solved by instance search using the only candidate"
            , nest 2 $ prettyTCM c <+> "=" <+> prettyTCM term
            , "of type " <+> prettyTCM t'
            , "for type" <+> prettyTCM t
            ]

          -- If we actually solved the constraints we should wake up any held
          -- instance constraints, to make sure we don't forget about them.
          wakeupInstanceConstraints
          return Nothing  -- We’re done

        _ -> do
          let cs = maybe cands (map fst . snd) mcands -- keep the current candidates if Nothing
          reportSDoc "tc.instance" 15 $
            text ("findInstance 5: refined candidates: ") <+>
            prettyTCM (List.map candidateTerm cs)
          whenProfile Profile.Instances $ tick "findInstance: multiple candidates"
          return (Just (cs, neverUnblock))

insidePi :: Type -> (Type -> TCM a) -> TCM a
insidePi t ret = reduce (unEl t) >>= \case
    Pi a b     -> addContext (absName b, a) $ insidePi (absBody b) ret
    Def{}      -> ret t
    Var{}      -> ret t
    Sort{}     -> __IMPOSSIBLE__
    Con{}      -> __IMPOSSIBLE__
    Lam{}      -> __IMPOSSIBLE__
    Lit{}      -> __IMPOSSIBLE__
    Level{}    -> __IMPOSSIBLE__
    MetaV{}    -> __IMPOSSIBLE__
    DontCare{} -> __IMPOSSIBLE__
    Dummy s _  -> __IMPOSSIBLE_VERBOSE__ s

-- | Apply the computation to every argument in turn by resetting the state every
--   time. Return the list of the arguments giving the result True.
--
--   If the resulting list contains exactly one element, then the state is the
--   same as the one obtained after running the corresponding computation. In
--   all the other cases, the state is reset.
--
--   Also returns the candidates that pass type checking but fails constraints,
--   so that the error messages can be reported if there are no successful
--   candidates.
filterResettingState
  :: MetaId
  -> [Candidate]
  -> (Candidate -> TCM YesNo)
  -> TCM ([(Candidate, TCErr)], [(Candidate, Term)])
filterResettingState m cands f = do
  ctxArgs  <- getContextArgs
  let ctxElims = map Apply ctxArgs
  result <- mapM (\c -> do bs <- localTCStateSaving (f c); return (c, bs)) cands

  -- Check that there aren't any hard failures
  case [ err | (_, (HellNo err, _)) <- result ] of
    err : _ -> throwError err
    []      -> return ()

  -- c : Candidate
  -- r : YesNo
  -- a : Type         (fully instantiated)
  -- s : TCState
  let
    result' = [ (c, v, s) | (c, (r, s)) <- result, v <- maybeToList (fromYes r) ]
    overlap = flip all result \(c, (r, s)) -> case r of
      Yes _ False -> False
      _ -> True
  result'' <- dropSameCandidates m overlap result'
  case result'' of
    [(c, v, s)] -> ([], [(c, v)]) <$ putTC s
    _           -> do
      let bad  = [ (c, err) | (c, (NoBecause err, _)) <- result ]
          good = [ (c, v) | (c, v, _) <- result'' ]
      return (bad, good)

-- | The state used to reduce a list of candidates according to the
-- overlap rules.
data OverlapState item = OverlapState
  { survivingCands :: [item]
    -- ^ The reduced list.

  , guardingCands  :: [Candidate]
    -- ^ Overlapping candidates that have been discarded, which are kept
    -- around because they might still discard some overlappable
    -- candidates.
  }

-- | Apply the instance overlap rules to reduce the list of candidates.
resolveInstanceOverlap
  :: forall item.
     Bool
  -> Relevance
  -> (item -> Candidate)
  -> [item]
  -> TCM [item]
resolveInstanceOverlap overlapOk rel itemC cands = wrapper where
  wrapper
    -- If the instance meta is irrelevant: anything will do, no reason
    -- to do any work.
    | isIrrelevant rel = pure cands

    -- If all the candidates are incoherent: choose the leftmost candidate.
    | all (isIncoherent . candidateOverlap . itemC) cands
    , (c:_) <- cands = pure [c]

    -- If all the candidates are record field overlap: choose the leftmost candidate.
    | all ((== FieldOverlap) . candidateOverlap . itemC) cands
    , (c:_) <- cands = pure [c]

    -- If none of the candidates have a special overlap mode: there's no
    -- reason to do any work.
    | all ((DefaultOverlap ==) . candidateOverlap . itemC) cands = pure cands

    | not overlapOk = pure cands

    -- If some of the candidates are overlappable/overlapping, then we
    -- should do the work.
    | otherwise = Bench.billTo [Bench.Typing, Bench.InstanceSearch, Bench.CheckOverlap] do
      reportSDoc "tc.instance.overlap" 30 $ "overlapping instances:" $$ vcat (map (debugCandidate . itemC) cands)

      chooseIncoherent . survivingCands <$> foldrM insert (OverlapState [] []) cands

  isGlobal Candidate{candidateKind = GlobalCandidate _} = True
  isGlobal _ = False

  -- At the end of the process, we might be in a situation where all
  -- candidates are incoherent, except for one, since the user might
  -- have an instance which fixes some arguments in a way that prevents
  -- it from serving as a specialisation (see test/Succeed/OverlapIncoherent1).
  --
  -- This non-incoherent candidate is what is chosen.
  chooseIncoherent :: [item] -> [item]
  chooseIncoherent cands = case List.partition (isIncoherent . itemC) cands of
    (as, [c]) | all (isGlobal . itemC) as -> pure c
    _                                     -> cands

  -- Insert a new item into the overlap state.
  insertNew
    :: OverlapState item  -- The state to insert into
    -> item               -- The item to insert
    -> [item]             -- Old items which we might overlap/be overlapped by
    -> TCM (OverlapState item)
  insertNew oldState new [] = pure oldState{ survivingCands = [new] }
  insertNew oldState newItem (oldItem:olds) = do
    let
      new = itemC newItem
      old = itemC oldItem

    reportSDoc "tc.instance.overlap" 50 $ vcat
      [ "comparing new candidate"
      , nest 2 (debugCandidate new)
      , "versus old candidate"
      , nest 2 (debugCandidate old)
      ]

    let
      -- If the new candidate overrides the old, drop it. But if the old
      -- candidate was overlapping (and the new one isn't), we keep it
      -- as a guard, since it might knock out future candidates.
      newold = insertNew oldState newItem olds <&> \case
        OverlapState items guards ->
          if not (isOverlapping new) && isOverlapping old
            then OverlapState items guards
            else OverlapState items (old:guards)

      -- If the old candidate overrides the new, then stop inserting.
      -- But if the new candidate is overlapping, it can be added as a
      -- guard.
      oldnew = do
        if isOverlapping old || not (isOverlapping new) then pure oldState else do
          let OverlapState{ survivingCands = oldItems, guardingCands = guards } = oldState
          reportSDoc "tc.instance.overlap" 40 $ vcat
            [ "will become guard:"
            , nest 2 (debugCandidate new)
            , "old items:"
            , nest 2 (vcat (map (debugCandidate . itemC) oldItems))
            ]

          -- But we can't /just/ add it to the list of guards: the new
          -- item might conflict with some of the other old candidates.
          -- We must remove those.
          alive <- filterM (fmap not . doesCandidateOverlap new . itemC) oldItems
          pure $ OverlapState alive (new:guards)

      -- If neither overrides the other, keep both!
      neither = insertNew oldState newItem olds <&> \case
        OverlapState items guards -> OverlapState (oldItem:items) guards

    ifM (new `doesCandidateOverlap` old)
      {- then -} newold
      {- else -} (ifM (old `doesCandidateOverlap` new)
        {- then -} oldnew
        {- else -} neither)

  -- Insert a new instance into the given overlap set.
  insert :: item -> OverlapState item -> TCM (OverlapState item)
  insert newItem oldState@(OverlapState oldItems guards) = do
    let new = itemC newItem
    -- If the new candidate is overridden by any of the guards, we can
    -- ditch it immediately.
    guarded <- anyM guards (`doesCandidateOverlap` new)

    reportSDoc "tc.instance.overlap" 40 $ vcat
      [ "inserting new candidate:"
      , nest 2 (debugCandidate new)
      , "against old candidates"
      , nest 2 (vcat (map (debugCandidate . itemC) oldItems))
      , "and guarding candidates"
      , nest 2 (vcat (map debugCandidate guards))
      , "is guarded?" <+> prettyTCM guarded
      ]

    if guarded then pure oldState else insertNew oldState newItem oldItems

-- Drop all candidates which are judgmentally equal to the first one.
-- This is sufficient to reduce the list to a singleton should all be equal.
dropSameCandidates :: MetaId -> Bool -> [(Candidate, Term, TCState)] -> TCM [(Candidate, Term, TCState)]
dropSameCandidates m overlapOk cands0 = verboseBracket "tc.instance" 30 "dropSameCandidates" $ do
  !nextMeta    <- nextLocalMeta
  isRemoteMeta <- isRemoteMeta

  -- Does "it" contain any fresh meta-variables?
  let freshMetas = getAny . allMetas (\m -> Any (not (isRemoteMeta m || m < nextMeta)))

  rel <- getRelevance <$> lookupMetaModality m

  -- Take overlappable candidates into account
  cands <- resolveInstanceOverlap overlapOk rel fst3 cands0
  reportSDoc "tc.instance.overlap" 30 $ "instances after resolving overlap:" $$ vcat (map (debugCandidate . fst3) cands)

  reportSDoc "tc.instance" 50 $ vcat
    [ "valid candidates:"
    , nest 2 $ vcat [ if freshMetas v then "(redacted)" else
                      sep [ prettyTCM v ]
                    | (_, v, _) <- cands ] ]

  case cands of
    [] -> return cands
    cvd : _ | isIrrelevant rel -> do
      reportSLn "tc.instance" 30 "dropSameCandidates: Meta is irrelevant so any candidate will do."
      return [cvd]
    cvd@(_, v, _) : vas
      | freshMetas v -> do
          reportSLn "tc.instance" 30 "dropSameCandidates: Solution of instance meta has fresh metas so we don't filter equal candidates yet"
          return (cvd : vas)
      | otherwise -> (cvd :) <$> dropWhileM equal vas
      where
        equal :: (Candidate, Term, a) -> TCM Bool
        equal (_, v', _)
            | freshMetas v' = return False  -- If there are fresh metas we can't compare
            | otherwise     =
          verboseBracket "tc.instance" 30 "dropSameCandidates: " $ do
          reportSDoc "tc.instance" 30 $ sep [ prettyTCM v <+> "==", nest 2 $ prettyTCM v' ]
          a <- uncurry piApplyM =<< ((,) <$> getMetaType m <*> getContextArgs)
          runBlocked (pureEqualTerm a v v') <&> \case
            Left{}  -> False
            Right b -> b

data YesNo = Yes Term Bool | No | NoBecause TCErr | HellNo TCErr
  deriving (Show)

fromYes :: YesNo -> Maybe Term
fromYes (Yes t _) = Just t
fromYes _         = Nothing

debugCandidate' :: MonadPretty m => Bool -> Bool -> Candidate -> m Doc
debugCandidate' raw term c@(Candidate q v t overlap) =
  let
    cand
      | term      = prettyTCM v
      | otherwise = prettyTCM c

    ty
      | raw       = nest 2 (pretty t)
      | otherwise = prettyTCM t

    head = fsep [ "-", pretty overlap, cand, ":" ]
  in if | raw       -> sep [ head, ty ]
        | otherwise -> head <+> ty

debugCandidate :: MonadPretty m => Candidate -> m Doc
debugCandidate = debugCandidate' False False

debugCandidateRaw :: MonadPretty m => Candidate -> m Doc
debugCandidateRaw = debugCandidate' True False

debugCandidateTerm :: MonadPretty m => Candidate -> m Doc
debugCandidateTerm = debugCandidate' False True

-- | Given a meta @m@ of type @t@ and a list of candidates @cands@,
-- @checkCandidates m t cands@ returns a refined list of valid candidates and
-- candidates that failed some constraints.
checkCandidates :: MetaId -> Type -> [Candidate] -> TCM (Maybe ([(Candidate, TCErr)], [(Candidate, Term)]))
checkCandidates m t cands =
  verboseBracket "tc.instance.candidates" 20 ("checkCandidates " ++ prettyShow m) $
  ifM (anyMetaTypes cands) (return Nothing) $ Just <$> do
    reportSDoc "tc.instance.candidates" 20 $ nest 2 $ "target:" <+> prettyTCM t
    reportSDoc "tc.instance.candidates" 20 $ nest 2 $ vcat
      [ "candidates", vcat (map debugCandidate cands) ]

    cands'@(_, okay) <- filterResettingState m cands (checkCandidateForMeta m t)

    reportSDoc "tc.instance.candidates" 20 $ nest 2 $ vcat
      [ "valid candidates", vcat (map (debugCandidate . fst) okay) ]
    reportSDoc "tc.instance.candidates" 60 $ nest 2 $ vcat
      [ "valid candidates", vcat (map (debugCandidateTerm . fst) okay) ]

    return cands'
  where
    anyMetaTypes :: [Candidate] -> TCM Bool
    anyMetaTypes [] = return False
    anyMetaTypes (Candidate _ _ a _ : cands) = do
      a <- instantiate a
      case unEl a of
        MetaV{} -> return True
        _       -> anyMetaTypes cands

    checkDepth :: Term -> Type -> TCM YesNo -> TCM YesNo
    checkDepth c a k = locallyTC eInstanceDepth succ $ do
      d        <- viewTC eInstanceDepth
      maxDepth <- maxInstanceSearchDepth
      when (d > maxDepth) $ typeError $ InstanceSearchDepthExhausted c a maxDepth
      k

    checkCandidateForMeta :: MetaId -> Type -> Candidate -> TCM YesNo
    checkCandidateForMeta m t (Candidate q term t' _) = checkDepth term t' $ do
      Bench.billTo [Bench.Typing, Bench.InstanceSearch, Bench.FilterCandidates] $ do
      whenProfile Profile.Instances $ tick "checkCandidateForMeta"

      -- Andreas, 2015-02-07: New metas should be created with range of the
      -- current instance meta, thus, we set the range.
      mv <- lookupLocalMeta m
      setCurrentRange mv $ runCandidateCheck $
        verboseBracket "tc.instance" 20 ("checkCandidateForMeta " ++ prettyShow m) $ do
          reportSDoc "tc.instance" 20 $ vcat
            [ "checkCandidateForMeta"
            , "  t    =" <+> prettyTCM t
            , "  t'   =" <+> prettyTCM t'
            , "  term =" <+> prettyTCM term
            ]
          reportSDoc "tc.instance" 70 $ vcat
            [ "  t    =" <+> pretty t
            , "  t'   =" <+> pretty t'
            , "  term =" <+> pretty term
            ]
          debugConstraints

          -- Apply hidden and instance arguments (in case of
          -- --overlapping-instances, this performs recursive
          -- inst. search!).
          (args, t'') <- implicitArgs (-1) (\h -> notVisible h) t'

          reportSDoc "tc.instance" 20 $
            "instance search: checking" <+> prettyTCM t'' <+> "<=" <+> prettyTCM t
          reportSDoc "tc.instance" 70 $ vcat
            [ "instance search: checking (raw)"
            , nest 4 $ pretty t''
            , nest 2 $ "<="
            , nest 4 $ pretty t
            ]

          -- Check whether this candidate is OK, and whether it is okay
          -- for the overlap check. For the candidate to be acceptable,
          -- its type must be a subtype of the goal type.
          (cons, overlapOk) <- ifNoConstraints_ (leqType t'' t) (pure ([], True)) \pid -> do
            -- To know if this candidate is safe for overlap, we have to
            -- check that it does not constrain the type of the instance
            -- goal. We can do this by running it in a new problem and
            -- checking whether the computation produced any constraints
            -- that are blocked by the instance goal.
            cons <- getConstraintsForProblem pid
            -- Make sure to put these constraints back if we end up
            -- solving the instance goal with this candidate.
            stealConstraints pid
            let
              blocking = foldMap (allBlockingMetas . constraintUnblocker) cons
              !ok = getAll $! flip allMetas t (All . not . flip Set.member blocking)
            pure (cons, ok)
          debugConstraints

          flip catchError (return . NoBecause) $ do
            -- make a pass over constraints, to detect cases where
            -- some are made unsolvable by the type comparison, but
            -- don't do this for FindInstance's to prevent loops.
            solveAwakeConstraints' True
            -- We need instantiateFull here to remove 'local' metas
            v <- instantiateFull =<< (term `applyDroppingParameters` args)
            reportSDoc "tc.instance" 15 $
              sep [ ("instance search: found solution for" <+> prettyTCM m) <> ":"
                  , nest 2 $ prettyTCM v ]

            reportSDoc "tc.instance.overlap" 30 $
              "candidate" <+> prettyTCM v <+> "okay for overlap?" <+> prettyTCM overlapOk
              $$ vcat (map prettyTCM cons)

            whenProfile Profile.Instances $ tick "checkCandidateForMeta: yes"
            return $ Yes v overlapOk
      where
        runCandidateCheck = flip catchError handle . nowConsideringInstance

        hardFailure :: TCErr -> Bool
        hardFailure (TypeError _ _ err) =
          case clValue err of
            InstanceSearchDepthExhausted{} -> True
            _                              -> False
        hardFailure _ = False

        handle :: TCErr -> TCM YesNo
        handle err
          | hardFailure err = do
            whenProfile Profile.Instances $ tick "checkCandidateForMeta: no"
            return $ HellNo err
          | otherwise       = do
            reportSDoc "tc.instance" 50 $ "candidate failed type check:" <+> prettyTCM err
            whenProfile Profile.Instances $ tick "checkCandidateForMeta: no"
            return No


nowConsideringInstance :: (ReadTCState m) => m a -> m a
nowConsideringInstance = locallyTCState stConsideringInstance $ const True

-- Rather than just the instance constraints, these are the constraints
-- which could be suspended by being under 'nowConsideringInstances',
-- which also includes unquote constraints.
isInstanceProblemConstraint :: ProblemConstraint -> Bool
isInstanceProblemConstraint c = case clValue (theConstraint c) of
  FindInstance{}  -> True
  UnquoteTactic{} -> True
  _ -> False

wakeupInstanceConstraints :: TCM ()
wakeupInstanceConstraints =
  unlessM shouldPostponeInstanceSearch $ do
    wakeConstraints (wakeUpWhen_ isInstanceProblemConstraint)
    solveAwakeInstanceConstraints

solveAwakeInstanceConstraints :: TCM ()
solveAwakeInstanceConstraints =
  solveSomeAwakeConstraints isInstanceProblemConstraint False

postponeInstanceConstraints :: TCM a -> TCM a
postponeInstanceConstraints m =
  locallyTCState stPostponeInstanceSearch (const True) m <* wakeupInstanceConstraints

-- | To preserve the invariant that a constructor is not applied to its
--   parameter arguments, we explicitly check whether function term
--   we are applying to arguments is a unapplied constructor.
--   In this case we drop the first 'conPars' arguments.
--   See Issue670a.
--   Andreas, 2013-11-07 Also do this for projections, see Issue670b.
applyDroppingParameters :: Term -> Args -> TCM Term
applyDroppingParameters t vs = do
  let fallback = return $ t `apply` vs
  case t of
    Con c ci [] -> do
      def <- theDef <$> getConInfo c
      case def of
        Constructor {conPars = n} -> return $ Con c ci (map Apply $ drop n vs)
        _ -> __IMPOSSIBLE__
    Def f [] -> do
      -- Andreas, 2022-03-07, issue #5809: don't drop parameters of irrelevant projections.
      mp <- isRelevantProjection f
      case mp of
        Just Projection{projIndex = n} -> do
          case drop n vs of
            []     -> return t
            u : us -> (`apply` us) <$> applyDef ProjPrefix f u
        _ -> fallback
    _ -> fallback

---------------------------------------------------------------------------
-- * Instance definitions
---------------------------------------------------------------------------

data OutputTypeName
  = OutputTypeName QName
  | OutputTypeVar
  | OutputTypeVisiblePi
  | OutputTypeNameNotYetKnown Blocker
  | NoOutputTypeName

-- | Strips all hidden and instance Pi's and return the argument
--   telescope, the head term, and its name, if possible.
getOutputTypeName :: Type -> TCM (Telescope, Term, OutputTypeName)
-- 2023-10-26, Jesper, issue #6941: To make instance search work correctly for
-- abstract or opaque instances, we need to ignore abstract mode when computing
-- the output type name.
getOutputTypeName t = ignoreAbstractMode $ do
  TelV tel t' <- telViewUpTo' (-1) notVisible t
  ifBlocked (unEl t') (\b t -> return (tel , __DUMMY_TERM__, OutputTypeNameNotYetKnown b)) $ \ _ v ->
    case v of
      -- Possible base types:
      Def n _  -> return (tel, v, OutputTypeName n)
      Sort{}   -> return (tel, v, NoOutputTypeName)
      Var n _  -> return (tel, v, OutputTypeVar)
      Pi{}     -> return (tel, v, OutputTypeVisiblePi)
      -- Not base types:
      Con{}    -> __IMPOSSIBLE__
      Lam{}    -> __IMPOSSIBLE__
      Lit{}    -> __IMPOSSIBLE__
      Level{}  -> __IMPOSSIBLE__
      MetaV{}  -> __IMPOSSIBLE__
      DontCare{} -> __IMPOSSIBLE__
      Dummy s _ -> __IMPOSSIBLE_VERBOSE__ s


-- | Register the definition with the given type as an instance.
--   Issue warnings if instance is unusable.
addTypedInstance ::
     QName  -- ^ Name of instance.
  -> Type   -- ^ Type of instance.
  -> TCM ()
addTypedInstance = addTypedInstance' True Nothing

-- | Register the definition with the given type as an instance.
addTypedInstance'
  :: Bool               -- ^ Should we print warnings for unusable instance declarations?
  -> Maybe InstanceInfo -- ^ Is this instance a copy?
  -> QName              -- ^ Name of instance.
  -> Type               -- ^ Type of instance.
  -> TCM ()
addTypedInstance' w orig x t = do
  reportSDoc "tc.instance.add" 30 $ vcat
    [ "adding typed instance" <+> prettyTCM x <+> "with type"
    , prettyTCM =<< flip abstract t <$> getContextTelescope
    ]

  (tel, hdt, n) <- getOutputTypeName t
  case n of
    OutputTypeName n -> addContext tel $ do
      tele <- getContextTelescope

      -- Insert the instance into the instance table, putting it in the
      -- discrimination tree *and* bumping the total number of instances
      -- for this class.

      tree <- insertDT (length tele) hdt x =<< getsTC (view stInstanceTree)
      setTCLens stInstanceTree tree

      modifyTCLens' (stSignature . sigInstances . itableCounts) $
        Map.insertWith (+) n 1

      let
        info = flip fromMaybe orig InstanceInfo
          { instanceClass   = n
          , instanceOverlap = DefaultOverlap
          }

      -- This is no longer used to build the instance table for imported
      -- modules, but it is still used to know if an instance should be
      -- copied when applying a section.
      modifySignature $ updateDefinition x \ d -> d { defInstance = Just info }

      -- If there's anything visible in the context, which will
      -- eventually end up in the instance's type, let's make a note to
      -- get rid of it before serialising the instance table.
      con <- isConstructor x
      -- However, do note that data constructors can have "visible
      -- arguments" in their global type which.. aren't actually
      -- visible: the parameters.
      when (any visible tele && not con) $ modifyTCLens' stTemporaryInstances $ Set.insert x

    OutputTypeNameNotYetKnown b -> do
      addUnknownInstance x
      addConstraint b $ ResolveInstanceHead x

    NoOutputTypeName    -> when w $ warning $ WrongInstanceDeclaration
    OutputTypeVar       -> when w $ warning $ WrongInstanceDeclaration
    OutputTypeVisiblePi -> when w $ warning $ InstanceWithExplicitArg x

resolveInstanceHead :: QName -> TCM ()
resolveInstanceHead q = do
  clearUnknownInstance q
  -- Andreas, 2022-12-04, issue #6380:
  -- Do not warn about unusable instances here.
  addTypedInstance' False Nothing q =<< typeOfConst q

-- | Try to solve the instance definitions whose type is not yet known, report
--   an error if it doesn't work and return the instance table otherwise.
getInstanceDefs :: TCM InstanceTable
getInstanceDefs = do
  insts <- getAllInstanceDefs
  unless (null $ snd insts) $
    typeError $ GenericError $ "There are instances whose type is still unsolved"
  return $ fst insts

-- | Prune an 'Interface' to remove any instances that would be
-- inapplicable in child modules.
--
-- While in a section with visible arguments, we add any instances
-- defined locally to the instance table: you have to be able to find
-- them, after all! Conservatively, all of the local variables are
-- turned into 'FlexK's, i.e., wildcards.
--
-- But when we leave such a section, these instances have no more value:
-- even though they might technically be in scope, their types are
-- malformed, since they have visible pis.
--
-- This function deletes these instances from the instance tree in the
-- given signature to save on serialisation time *and* time spent
-- checking for candidate validity in client modules. It can't do this
-- directly in the TC state to prevent these instances from going out of
-- scope before interaction (see #7196).
pruneTemporaryInstances :: Interface -> TCM Interface
pruneTemporaryInstances int = do
  todo <- useTC stTemporaryInstances

  reportSDoc "tc.instance.prune" 30 $ vcat
    [ "leaving section"
    , prettyTCM =<< getContextTelescope
    , "todo:" <+> prettyTCM todo
    ]

  let sig' = over (sigInstances . itableTree) (flip deleteFromDT todo) (iSignature int)
  pure int{ iSignature = sig' }


module Agda.TypeChecking.Generalize
  ( generalizeType
  , generalizeType'
  , generalizeTelescope ) where

import Prelude hiding (null)

import Control.Arrow (first)
import Control.Monad
import Control.Monad.Except

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (partition, sortBy)
import Data.Monoid
import Data.Function (on)

import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name (LensInScope(..))
import Agda.Syntax.Position
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic
import Agda.Syntax.Internal.MetaVars
import Agda.Syntax.Scope.Monad (bindVariable, outsideLocalVars)
import Agda.Syntax.Scope.Base (BindingSource(..))
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Free
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.InstanceArguments (postponeInstanceConstraints)
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Warnings

import Agda.Benchmarking (Phase(Typing, Generalize))
import Agda.Utils.Benchmark
import qualified Agda.Utils.BiMap as BiMap
import Agda.Utils.Functor
import Agda.Utils.Impossible
import Agda.Utils.List   (hasElem)
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Size
import Agda.Utils.Permutation
import Agda.Utils.Pretty (prettyShow)


-- | Generalize a telescope over a set of generalizable variables.
generalizeTelescope :: Map QName Name -> (forall a. (Telescope -> TCM a) -> TCM a) -> ([Maybe Name] -> Telescope -> TCM a) -> TCM a
generalizeTelescope vars typecheckAction ret | Map.null vars = typecheckAction (ret [])
generalizeTelescope vars typecheckAction ret = billTo [Typing, Generalize] $ withGenRecVar $ \ genRecMeta -> do
  let s = Map.keysSet vars
  ((cxtNames, tel, letbinds), namedMetas, allmetas) <-
    createMetasAndTypeCheck s $ typecheckAction $ \ tel -> do
      cxt <- take (size tel) <$> getContext
      lbs <- getLetBindings -- This gives let-bindings valid in the current context
      return (map (fst . unDom) cxt, tel, lbs)
  -- Translate the QName to the corresponding bound variable
  (genTel, genTelNames, sub) <- computeGeneralization genRecMeta namedMetas allmetas

  let boundVar q = fromMaybe __IMPOSSIBLE__ $ Map.lookup q vars
      genTelVars = (map . fmap) boundVar genTelNames

  tel' <- applySubst sub <$> instantiateFull tel

  -- This is not so nice. When changing the context from Γ (r : R) to Γ Δ we need to do this at the
  -- level of contexts (as a Context -> Context function), so we repeat the name logic here. Take
  -- care to preserve the name of named generalized variables.
  let setName name d = first (const name) <$> d
      cxtEntry (mname, d) = do
          name <- maybe (setNotInScope <$> freshName_ s) return mname
          return $ setName name d
        where s  = fst $ unDom d
      dropCxt err = updateContext (strengthenS err 1) (drop 1)
  genTelCxt <- dropCxt __IMPOSSIBLE__ $ mapM cxtEntry $ reverse $ zip genTelVars $ telToList genTel

  -- For the explicit module telescope we get the names from the typecheck
  -- action.
  let newTelCxt = zipWith setName cxtNames $ reverse $ telToList tel'

  -- We are in context Γ (r : R) and should call the continuation in context Γ Δ Θρ passing it Δ Θρ
  -- We have
  --   Γ (r : R) ⊢ Θ            Θ = tel
  --   Γ ⊢ Δ                    Δ = genTel
  --   Γ Δ ⊢ ρ : Γ (r : R)      ρ = sub
  --   Γ ⊢ Δ Θρ                 Θρ = tel'
  -- And we shouldn't forget about the let-bindings (#3470)
  --   Γ (r : R) Θ ⊢ letbinds
  --   Γ Δ Θρ      ⊢ letbinds' = letbinds(lift |Θ| ρ)
  letbinds' <- applySubst (liftS (size tel) sub) <$> instantiateFull letbinds
  let addLet (x, (v, dom)) = addLetBinding' x v dom

  updateContext sub ((genTelCxt ++) . drop 1) $
    updateContext (raiseS (size tel')) (newTelCxt ++) $
      foldr addLet (ret genTelVars $ abstract genTel tel') letbinds'


-- | Generalize a type over a set of (used) generalizable variables.
generalizeType :: Set QName -> TCM Type -> TCM ([Maybe QName], Type)
generalizeType s typecheckAction = do
  (ns, t, _) <- generalizeType' s $ (,()) <$> typecheckAction
  return (ns, t)

-- | Allow returning additional information from the type checking action.
generalizeType' :: Set QName -> TCM (Type, a) -> TCM ([Maybe QName], Type, a)
generalizeType' s typecheckAction = billTo [Typing, Generalize] $ withGenRecVar $ \ genRecMeta -> do

  ((t, userdata), namedMetas, allmetas) <- createMetasAndTypeCheck s typecheckAction
  (genTel, genTelNames, sub) <- computeGeneralization genRecMeta namedMetas allmetas

  t' <- abstract genTel . applySubst sub <$> instantiateFull t

  reportSDoc "tc.generalize" 40 $ vcat
    [ "generalized"
    , nest 2 $ "t =" <+> escapeContext impossible 1 (prettyTCM t') ]

  return (genTelNames, t', userdata)

-- | Create metas for the generalizable variables and run the type check action.
createMetasAndTypeCheck :: Set QName -> TCM a -> TCM (a, Map MetaId QName, IntSet)
createMetasAndTypeCheck s typecheckAction = do
  ((namedMetas, x), allmetas) <- metasCreatedBy $ do
    (metamap, genvals) <- createGenValues s
    x <- locallyTC eGeneralizedVars (const genvals) typecheckAction
    return (metamap, x)
  return (x, namedMetas, allmetas)

-- | Add a placeholder variable that will be substituted with a record value packing up all the
--   generalized variables.
withGenRecVar :: (Type -> TCM a) -> TCM a
withGenRecVar ret = do
  -- Create a meta type (in Set₀) for the telescope record. It won't
  -- necessarily fit in Set₀, but since it's only used locally the sort
  -- shouldn't matter. Another option would be to put it in Setω, which is a
  -- bit more honest, but this leads to performance problems (see #3306).
  genRecMeta <- newTypeMeta (mkType 0)
  addContext (defaultDom ("genTel" :: String, genRecMeta)) $ ret genRecMeta

-- | Compute the generalized telescope from metas created when checking the type/telescope to be
--   generalized. Called in the context extended with the telescope record variable (whose type is
--   the first argument). Returns the telescope of generalized variables and a substitution from
--   this telescope to the current context.
computeGeneralization :: Type -> Map MetaId name -> IntSet -> TCM (Telescope, [Maybe name], Substitution)
computeGeneralization genRecMeta nameMap allmetas = postponeInstanceConstraints $ do

  reportSDoc "tc.generalize" 10 $ "computing generalization for type" <+> prettyTCM genRecMeta

  -- Pair metas with their metaInfo
  mvs <- mapM ((\ x -> (x,) <$> lookupMeta x) . MetaId) $ IntSet.toList allmetas

  -- Issue 4727: filter out metavariables that were created before the
  -- current checkpoint, since they are too old to be generalized.
  -- TODO: make metasCreatedBy smarter so it doesn't see pruned
  -- versions of old metas as new metas.
  cp <- viewTC eCurrentCheckpoint
  let isFreshMeta (x,mv) = enterClosure mv $ \ _ -> isJust <$> checkpointSubstitution' cp
  mvs <- filterM isFreshMeta mvs
  cs <- (++) <$> useTC stAwakeConstraints
             <*> useTC stSleepingConstraints

  reportSDoc "tc.generalize" 50 $ "current constraints:" <?> vcat (map prettyTCM cs)

  constrainedMetas <- Set.unions <$> mapM (constraintMetas . clValue . theConstraint) cs

  reportSDoc "tc.generalize" 30 $ nest 2 $
    "constrainedMetas     = " <+> prettyList_ (map prettyTCM $ Set.toList constrainedMetas)

  let isConstrained x = Set.member x constrainedMetas
      -- Note: Always generalize named metas even if they are constrained. We
      -- freeze them so they won't be instantiated by the constraint, and we do
      -- want the nice error from checking the constraint after generalization.
      -- See #3276.
      isGeneralizable (x, mv) = Map.member x nameMap ||
                                not (isConstrained x) && NoGeneralize /= unArg (miGeneralizable (mvInfo mv))
      isSort = isSortMeta_ . snd
      isOpen = isOpenMeta . mvInstantiation . snd

  -- Split the generalizable metas in open and closed
  let (generalizable, nongeneralizable)         = partition isGeneralizable mvs
      (generalizableOpen', generalizableClosed) = partition isOpen generalizable
      (openSortMetas, generalizableOpen)        = partition isSort generalizableOpen'
      nongeneralizableOpen                      = filter isOpen nongeneralizable

  reportSDoc "tc.generalize" 30 $ nest 2 $ vcat
    [ "generalizable        = " <+> prettyList_ (map (prettyTCM . fst) generalizable)
    , "generalizableOpen    = " <+> prettyList_ (map (prettyTCM . fst) generalizableOpen)
    , "openSortMetas        = " <+> prettyList_ (map (prettyTCM . fst) openSortMetas)
    ]

  -- Issue 3301: We can't generalize over sorts
  unlessNull openSortMetas $ \ ms ->
    warning $ CantGeneralizeOverSorts $ map fst ms

  -- Any meta in the solution of a generalizable meta should be generalized over (if possible).
  cp <- viewTC eCurrentCheckpoint
  let canGeneralize x | isConstrained x = return False
      canGeneralize x = do
          mv   <- lookupMeta x
          msub <- enterClosure mv $ \ _ ->
                    checkpointSubstitution' cp
          let sameContext =
                -- We can only generalize if the metavariable takes the context variables of the
                -- current context as arguments. This happens either when the context of the meta
                -- is the same as the current context and there is no pruning, or the meta context
                -- is a weakening but the extra variables have been pruned.
                -- It would be possible to generalize also in the case when some context variables
                -- (other than genTel) have been pruned, but it's hard to construct an example
                -- where this actually happens.
                case (msub, mvPermutation mv) of
                  (Just IdS, Perm m xs)        -> xs == [0 .. m - 1]
                  (Just (Wk n IdS), Perm m xs) -> xs == [0 .. m - n - 1]
                  _                            -> False
          unless sameContext $ do
            ty <- getMetaType x
            let Perm m xs = mvPermutation mv
            reportSDoc "tc.generalize" 20 $ vcat
              [ text "Don't know how to generalize over"
              , nest 2 $ prettyTCM x <+> text ":" <+> prettyTCM ty
              , text "in context"
              , nest 2 $ inTopContext . prettyTCM =<< getContextTelescope
              , text "permutation:" <+> text (show (m, xs))
              , text "subst:" <+> pretty msub ]
          return sameContext
  inherited <- fmap Set.unions $ forM generalizableClosed $ \ (x, mv) ->
    case mvInstantiation mv of
      InstV _ v -> do
        parentName <- getMetaNameSuggestion x
        metas <- filterM canGeneralize . Set.toList . allMetas Set.singleton =<< instantiateFull v
        let suggestNames i [] = return ()
            suggestNames i (m : ms) = do
              -- #4291: Override existing meta name suggestion. If we solved the parent with a new
              --        meta use the parent name for that, otherwise suffix with a number.
              let suf | null ms && i == 1, MetaV{} <- v = ""
                      | otherwise                       = "." ++ show i
              setMetaNameSuggestion m (parentName ++ suf)
              suggestNames (i + 1) ms
        unless (null metas) $
          reportSDoc "tc.generalize" 40 $ hcat ["Inherited metas from ", prettyTCM x, ":"] <?> prettyList_ (map prettyTCM metas)
                                    -- Don't suggest names for explicitly named generalizable metas
        Set.fromList metas <$ suggestNames 1 (filter (`Map.notMember` nameMap) metas)
      _ -> __IMPOSSIBLE__

  let (alsoGeneralize, reallyDontGeneralize) = partition (`Set.member` inherited) $ map fst nongeneralizableOpen
      generalizeOver   = map fst generalizableOpen ++ alsoGeneralize
      shouldGeneralize = (generalizeOver `hasElem`)

  reportSDoc "tc.generalize" 30 $ nest 2 $ vcat
    [ "alsoGeneralize       = " <+> prettyList_ (map prettyTCM alsoGeneralize)
    , "reallyDontGeneralize = " <+> prettyList_ (map prettyTCM reallyDontGeneralize)
    ]

  reportSDoc "tc.generalize" 10 $ "we're generalizing over" <+> prettyList_ (map prettyTCM generalizeOver)

  -- Sort metas in dependency order. Include open metas that we are not
  -- generalizing over, since they will need to be pruned appropriately (see
  -- Issue 3672).
  allSortedMetas <- fromMaybeM (typeError GeneralizeCyclicDependency) $
    dependencySortMetas (generalizeOver ++ reallyDontGeneralize ++ map fst openSortMetas)
  let sortedMetas = filter shouldGeneralize allSortedMetas

  let dropCxt err = updateContext (strengthenS err 1) (drop 1)

  -- Create the pre-record type (we don't yet know the types of the fields)
  (genRecName, genRecCon, genRecFields) <- dropCxt __IMPOSSIBLE__ $
      createGenRecordType genRecMeta sortedMetas

  reportSDoc "tc.generalize" 30 $ vcat $
    [ "created genRecordType"
    , nest 2 $ "genRecName   = " <+> prettyTCM genRecName
    , nest 2 $ "genRecCon    = " <+> prettyTCM genRecCon
    , nest 2 $ "genRecFields = " <+> prettyList_ (map prettyTCM genRecFields)
    ]

  -- Solve the generalizable metas. Each generalizable meta is solved by projecting the
  -- corresponding field from the genTel record.
  cxtTel <- getContextTelescope
  let solve m field = do
        reportSDoc "tc.generalize" 30 $ "solving generalized meta" <+>
          prettyTCM m <+> ":=" <+> prettyTCM (Var 0 [Proj ProjSystem field])
        -- m should not be instantiated, but if we don't check constraints
        -- properly it could be (#3666 and #3667). Fail hard instead of
        -- generating bogus types.
        whenM (isInstantiatedMeta m) __IMPOSSIBLE__
        assignTerm' m (telToArgs cxtTel) $ Var 0 [Proj ProjSystem field]
  zipWithM_ solve sortedMetas genRecFields

  -- Record the named variables in the telescope
  let telNames = map (`Map.lookup` nameMap) sortedMetas

  -- Build the telescope of generalized metas
  teleTypes <- do
    args <- getContextArgs
    fmap concat $ forM sortedMetas $ \ m -> do
      mv   <- lookupMeta m
      let info =
            hideOrKeepInstance $
            getArgInfo $ miGeneralizable $ mvInfo mv
          HasType{ jMetaType = t } = mvJudgement mv
          perm = mvPermutation mv
      t' <- piApplyM t $ permute (takeP (length args) perm) args
      return [(Arg info $ miNameSuggestion $ mvInfo mv, t')]
  let genTel = buildGeneralizeTel genRecCon teleTypes

  reportSDoc "tc.generalize" 40 $ vcat
    [ text "genTel =" <+> prettyTCM genTel ]

  -- Now we need to prune the unsolved metas to make sure they respect the new
  -- dependencies (#3672). Also update interaction points to point to pruned metas.
  let inscope (ii, InteractionPoint{ipMeta = Just x})
        | IntSet.member (metaId x) allmetas = Just (x, ii)
      inscope _ = Nothing
  ips <- Map.fromDistinctAscList . mapMaybe inscope . fst . BiMap.toDistinctAscendingLists <$> useTC stInteractionPoints
  pruneUnsolvedMetas genRecName genRecCon genTel genRecFields ips shouldGeneralize allSortedMetas

  -- Fill in the missing details of the telescope record.
  dropCxt __IMPOSSIBLE__ $ fillInGenRecordDetails genRecName genRecCon genRecFields genRecMeta genTel

  -- Now abstract over the telescope. We need to apply the substitution that subsitutes a record
  -- value packing up the generalized variables for the genTel variable.
  let sub = unpackSub genRecCon (map (argInfo . fst) teleTypes) (length teleTypes)

  return (genTel, telNames, sub)

-- | Prune unsolved metas (#3672). The input includes also the generalized metas and is sorted in
-- dependency order. The telescope is the generalized telescope.
pruneUnsolvedMetas :: QName -> ConHead -> Telescope -> [QName] -> Map MetaId InteractionId -> (MetaId -> Bool) -> [MetaId] -> TCM ()
pruneUnsolvedMetas genRecName genRecCon genTel genRecFields interactionPoints isGeneralized metas
  | all isGeneralized metas = return ()
  | otherwise               = prune [] genTel metas
  where
    prune _ _ [] = return ()
    prune cxt tel (x : xs) | not (isGeneralized x) = do
      -- If x is a blocked term we shouldn't instantiate it.
      whenM (not <$> isBlockedTerm x) $ do
        x <- if size tel > 0 then prePrune x
                             else return x
        pruneMeta (telFromList $ reverse cxt) x
      prune cxt tel xs
    prune cxt (ExtendTel a tel) (x : xs) = prune (fmap (x,) a : cxt) (unAbs tel) xs
      where x = absName tel
    prune _ _ _ = __IMPOSSIBLE__

    sub = unpackSub genRecCon $ map getArgInfo $ telToList genTel

    prepruneErrorRefinedContext = prepruneError $
      "Failed to generalize because some of the generalized variables depend on an " ++
      "unsolved meta created in a refined context (not a simple extension of the context where " ++
      "generalization happens)."

    prepruneErrorCyclicDependencies = prepruneError $
      "Failed to generalize due to circular dependencies between the generalized " ++
      "variables and an unsolved meta."

    prepruneErrorFailedToInstantiate = prepruneError $
      "Failed to generalize because the generalized variables depend on an unsolved meta " ++
      "that could not be lifted outside the generalization."

    prepruneError :: String -> MetaId -> TCM a
    prepruneError msg x = do
      r <- getMetaRange x
      genericDocError =<<
        (fwords (msg ++ " The problematic unsolved meta is") $$
                 (nest 2 $ prettyTCM (MetaV x []) <+> "at" <+> pretty r)
        )

    -- If one of the fields depend on this meta, we have to make sure that this meta doesn't depend
    -- on any variables introduced after the genRec. See test/Fail/Issue3672b.agda for a test case.
    prePrune x = do
      cp <- viewTC eCurrentCheckpoint
      mv <- lookupMeta x
      (i, _A) <- enterClosure mv $ \ _ -> do
        δ <- checkpointSubstitution cp
        _A <- case mvJudgement mv of
                IsSort{}  -> return Nothing
                HasType{} -> Just <$> getMetaTypeInContext x
        case δ of
          Wk n IdS -> return (n, _A)
          IdS      -> return (0, _A)
          _        -> prepruneErrorRefinedContext x
      if i == 0 then return x else do
        reportSDoc "tc.generalize.prune.pre" 40 $ vcat
          [ "prepruning"
          , nest 2 $ pretty x <+> ":" <+> pretty (jMetaType $ mvJudgement mv)
          , nest 2 $ "|Δ| =" <+> pshow i ]

        -- We have
        --   Γ (r : GenRec)            current context
        --   Γ (r : GenRec) Δ ⊢ x : A  with |Δ| = i
        -- and we need to get rid of the dependency on Δ.

        -- We can only do this if A does not depend on Δ, so check this first.
        case IntSet.minView (allFreeVars _A) of
          Just (j, _) | j < i -> prepruneErrorCyclicDependencies x
          _                   -> return ()

        -- If it doesn't we can strenghten it to the current context (this is done by
        -- newMetaFromOld).
        --   Γ (r : GenRec) ⊢ ρ : Γ (r : GenRec) Δ
        let ρ  = strengthenS impossible i
            ρ' = raiseS i

        (y, u) <- newMetaFromOld mv ρ _A

        let uρ' = applySubst ρ' u

        reportSDoc "tc.generalize.prune.pre" 40 $ nest 2 $ vcat
          [ "u    =" <+> pretty u
          , "uρ⁻¹ =" <+> pretty uρ' ]

        -- To solve it we enter the context of x again
        enterClosure mv $ \ _ -> do
          -- v is x applied to the context variables
          v <- case _A of
                 Nothing -> Sort . MetaS x . map Apply <$> getMetaContextArgs mv
                 Just{}  -> MetaV x . map Apply <$> getMetaContextArgs mv
          noConstraints (doPrune x mv _A v uρ') `catchError` \ _ -> prepruneErrorFailedToInstantiate x
          setInteractionPoint x y
          return y

    pruneMeta _Θ x = do
      cp <- viewTC eCurrentCheckpoint
      mv <- lookupMeta x
      -- The reason we are doing all this inside the closure of x is so that if x is an interaction
      -- meta we get the right context for the pruned interaction meta.
      enterClosure mv $ \ _ ->
        -- If we can't find the generalized record, it's already been pruned and we don't have to do
        -- anything.
        whenJustM (findGenRec mv) $ \ i -> do

        reportSDoc "tc.generalize.prune" 30 $ vcat
          [ "pruning"
          , nest 2 $ inTopContext $ prettyTCM (mvJudgement mv)
          , nest 2 $ "GenRecTel is var" <+> pretty i ]

        _ΓrΔ <- getContextTelescope
        let (_Γ, _Δ) = (telFromList gs, telFromList ds)
              where (gs, _ : ds) = splitAt (size _ΓrΔ - i - 1) (telToList _ΓrΔ)

        -- Get the type of x. By doing this here we let the checkpoint machinery sort out the
        _A <- case mvJudgement mv of
                IsSort{}  -> return Nothing
                HasType{} -> Just <$> getMetaTypeInContext x

        -- We have
        --   Γ  (r : GenTel) Δ         current context
        --   Γ₀ (r : GenTel)           top context
        --   Γ₀ ⊢ Θ                    prefix of the generalized telescope currently in scope
        --   Γ (r : GenTel) Δ ⊢ x : A  the meta to prune

        -- Get the substitution from the point of generalization to the current context. This always
        -- succeeds since if the meta depends on GenTel it must have been created inside the
        -- generalization:
        --   Γ (r : GenTel) Δ ⊢ δ : Γ₀ (r : GenTel)
        δ <- checkpointSubstitution cp

        -- v is x applied to the context variables
        v <- case _A of
               Nothing -> Sort . MetaS x . map Apply <$> getMetaContextArgs mv
               Just{}  -> MetaV x . map Apply <$> getMetaContextArgs mv

        -- Now ultimately we want to create the fresh meta in the context
        --   Γ Θγ Δσ where Γ    ⊢ γ : Γ₀
        --                 Γ Θγ ⊢ σ : Γ (r : GenTel)
        -- σ is the unpacking substitution (which is polymorphic in Γ)
        let σ   = sub (size _Θ)
            --    Γ <- Γ (r : GenTel) Δ <- Γ₀ (r : GenTel) <- Γ₀
            γ   = strengthenS impossible (i + 1) `composeS` δ `composeS` raiseS 1
            _Θγ = applySubst γ _Θ
            _Δσ = applySubst σ _Δ

        -- The substitution into the new context is simply lifting σ over Δ:
        --   Γ Θγ Δσ ⊢ lift i σ : Γ (r : GenTel) Δ
        let ρ  = liftS i σ
            -- We also need ρ⁻¹, which is a lot easier to construct.
            ρ' = liftS i $ [ Var 0 [Proj ProjSystem fld] | fld <- reverse $ take (size _Θ) $ genRecFields ] ++# raiseS 1

        reportSDoc "tc.generalize.prune" 30 $ nest 2 $ vcat
          [ "Γ   =" <+> pretty _Γ
          , "Θ   =" <+> pretty _Θ
          , "Δ   =" <+> pretty _Δ
          , "σ   =" <+> pretty σ
          , "γ   =" <+> pretty γ
          , "δ   =" <+> pretty δ
          , "ρ   =" <+> pretty ρ
          , "ρ⁻¹ =" <+> pretty ρ'
          , "Θγ  =" <+> pretty _Θγ
          , "Δσ  =" <+> pretty _Δσ
          , "_A  =" <+> pretty _A
          ]

        -- When updating the context we also need to pick names for the variables. Get them from the
        -- current context and generate fresh ones for the generalized variables in Θ.
        (newCxt, rΘ) <- do
          (rΔ, _ : rΓ) <- splitAt i <$> getContext
          let setName = traverse $ \ (s, ty) -> (,ty) <$> freshName_ s
          rΘ <- mapM setName $ reverse $ telToList _Θγ
          let rΔσ = zipWith (\ name dom -> first (const name) <$> dom)
                            (map (fst . unDom) rΔ)
                            (reverse $ telToList _Δσ)
          return (rΔσ ++ rΘ ++ rΓ, rΘ)

        -- Now we can enter the new context and create our meta variable.
        (y, u) <- updateContext ρ (const newCxt) $ localScope $ do

          -- First, we add the named variables to the scope, to allow
          -- them to be used in holes (#3341). These should go outside Δ (#3735).
          outsideLocalVars i $ addNamedVariablesToScope rΘ

          -- Now we can create the new meta
          newMetaFromOld mv ρ _A

        -- Finally we solve x := yρ⁻¹. The reason for solving it this way instead of xρ := y is that
        -- ρ contains dummy terms for the variables that are not in scope.
        -- If x has been instantiated by some constraint unblocked by previous pruning or
        -- generalization, use equalTerm instead of assigning to x. If this fails (see
        -- test/Fail/Issue3655b.agda for a test case), we need to give an error. This can happen if
        -- there are dependencies between generalized variables that are hidden by constraints and
        -- the dependency sorting happens to pick the wrong order. For instance, if we have
        --    α : Nat   (unsolved meta)
        --    t : F α   (named variable)
        --    n : Nat   (named variable)
        -- and a constraint F α == F n, where F does some pattern matching preventing the constraint
        -- to be solved when n is still a meta. If t appears before n in the type these will be sorted
        -- as α, t, n, but we will solve α := n before we get to the pruning here. It's good that we
        -- solve first though, because that means we can give a more informative error message than
        -- the "Cannot instantiate..." we would otherwise get.
        let uρ' = applySubst ρ' u
        reportSDoc "tc.generalize.prune" 80 $ vcat
          [ "solving"
          , nest 2 $ sep [ pretty v   <+> "=="
                         , pretty uρ' <+> ":"
                         , pretty _A ] ]
        noConstraints (doPrune x mv _A v uρ') `catchError` niceError x v

        reportSDoc "tc.generalize.prune" 80 $ vcat
          [ "solved"
          , nest 2 $ "v    =" <+> (pretty =<< instantiateFull v)
          , nest 2 $ "uρ⁻¹ =" <+> (pretty =<< instantiateFull uρ') ]

        setInteractionPoint x y

    findGenRec :: MetaVariable -> TCM (Maybe Int)
    findGenRec mv = do
      cxt <- instantiateFull =<< getContext
      let notPruned = permute (takeP (length cxt) $ mvPermutation mv) $
               reverse $ zipWith const [0..] cxt
      case [ i | (i, Dom{unDom = (_, El _ (Def q _))}) <- zip [0..] cxt,
                 q == genRecName, i `elem` notPruned ] of
        []    -> return Nothing
        _:_:_ -> __IMPOSSIBLE__
        [i]   -> return (Just i)
                                                    -- Nothing if sort meta
    newMetaFromOld :: MetaVariable -> Substitution -> Maybe Type -> TCM (MetaId, Term)
    newMetaFromOld mv ρ mA = setCurrentRange mv $
      case mA of
        Nothing -> do
          s@(MetaS y _) <- newSortMeta
          return (y, Sort s)
        Just _A -> do
          let _Aρ = applySubst ρ _A
          newNamedValueMeta DontRunMetaOccursCheck
                            (miNameSuggestion $ mvInfo mv)
                            (jComparison $ mvJudgement mv) _Aρ

    -- If x is a hole, update the hole to point to y instead.
    setInteractionPoint x y =
      whenJust (Map.lookup x interactionPoints) (`connectInteractionPoint` y)

    doPrune :: MetaId -> MetaVariable -> Maybe Type -> Term -> Term -> TCM ()
    doPrune x mv mt v u =
      case mt of
        _ | isOpen -> assign DirEq x (getArgs v) u $ maybe AsTypes AsTermsOf mt
        Nothing    -> equalSort (unwrapSort v) (unwrapSort u)
        Just t     -> equalTerm t v u
      where
        isOpen = isOpenMeta $ mvInstantiation mv
        getArgs = \case
            Sort (MetaS _ es) -> fromMaybe __IMPOSSIBLE__ $ allApplyElims es
            MetaV _ es        -> fromMaybe __IMPOSSIBLE__ $ allApplyElims es
            _                 -> __IMPOSSIBLE__
        unwrapSort (Sort s) = s
        unwrapSort _        = __IMPOSSIBLE__

    niceError x u err = do
      u <- instantiateFull u
      let err' = case err of
                   TypeError{tcErrClosErr = cl} ->
                     -- Remove the 'when' part from the error since it's most like the same as ours.
                     err{ tcErrClosErr = cl{ clEnv = (clEnv cl) { envCall = Nothing } } }
                   _ -> err
          telList = telToList genTel
          names   = map (fst . unDom) telList
          late    = map (fst . unDom) $ filter (getAny . allMetas (Any . (== x))) telList
          projs (Proj _ q)
            | q `elem` genRecFields = Set.fromList $ catMaybes [getGeneralizedFieldName q]
          projs _                 = Set.empty
          early = Set.toList $ flip foldTerm u $ \ case
                  Var _ es   -> foldMap projs es
                  Def _ es   -> foldMap projs es
                  MetaV _ es -> foldMap projs es
                  _          -> Set.empty
          commas []       = __IMPOSSIBLE__
          commas [x]      = x
          commas [x, y]   = x ++ ", and " ++ y
          commas (x : xs) = x ++ ", " ++ commas xs
          cause = "There were unsolved constraints that obscured the " ++
                  "dependencies between the generalized variables."
          solution = "The most reliable solution is to provide enough information to make the dependencies " ++
                     "clear, but simply mentioning the variables in the right order should also work."
          order = sep [ fwords "Dependency analysis suggested this (likely incorrect) order:",
                        nest 2 $ fwords (unwords names) ]
          guess = "After constraint solving it looks like " ++ commas late ++ " actually depend" ++ s ++
                  " on " ++ commas early
            where
              s | length late == 1 = "s"
                | otherwise        = ""
      genericDocError =<< vcat
        [ fwords $ "Variable generalization failed."
        , nest 2 $ sep ["- Probable cause", nest 4 $ fwords cause]
        , nest 2 $ sep ["- Suggestion", nest 4 $ fwords solution]
        , nest 2 $ sep $ ["- Further information"
                         , nest 2 $ "-" <+> order ] ++
                         [ nest 2 $ "-" <+> fwords guess | not (null late), not (null early) ] ++
                         [ nest 2 $ "-" <+> sep [ fwords "The dependency I error is", prettyTCM err' ] ]
        ]

    addNamedVariablesToScope cxt =
      forM_ cxt $ \ Dom{ unDom = (x, _) } -> do
        -- Recognize named variables by lack of '.' (TODO: hacky!)
        reportSLn "tc.generalize.eta.scope" 40 $ "Adding (or not) " ++ prettyShow (nameConcrete x) ++ " to the scope"
        when ('.' `notElem` prettyShow (nameConcrete x)) $ do
          reportSLn "tc.generalize.eta.scope" 40 "  (added)"
          bindVariable LambdaBound (nameConcrete x) x

-- | Create a substition from a context where the i first record fields are variables to a context
--   where you have a single variable of the record type. Packs up the field variables in a record
--   constructor and pads with __DUMMY_TERM__s for the missing fields. Important that you apply this
--   to terms that only projects the defined fields from the record variable.
--   Used with partial record values when building the telescope of generalized variables in which
--   case we have done the dependency analysis that guarantees it is safe.
unpackSub :: ConHead -> [ArgInfo] -> Int -> Substitution
unpackSub con infos i = recSub
  where
    ar = length infos
    appl info v = Apply (Arg info v)
    recVal = Con con ConOSystem $ zipWith appl infos $ [var j | j <- [i - 1, i - 2..0]] ++ replicate (ar - i) __DUMMY_TERM__

    -- want: Γ Δᵢ ⊢ recSub i : Γ (r : R)
    -- have:
    -- Γ Δᵢ ⊢ recVal i :# σ : Θ (r : R),  if Γ Δᵢ ⊢ σ : Θ
    -- Γ Δᵢ ⊢ WkS i IdS : Γ
    recSub = recVal :# Wk i IdS

-- | Takes the list of types
--    A₁ []
--    A₂ [r.f₁]
--    A₃ [r.f₂, r.f₃]
--    ...
--   And builds the telescope
--    (x₁ : A₁ [ r := c _       .. _ ])
--    (x₂ : A₂ [ r := c x₁ _    .. _ ])
--    (x₃ : A₃ [ r := c x₁ x₂ _ .. _ ])
--    ...
buildGeneralizeTel :: ConHead -> [(Arg String, Type)] -> Telescope
buildGeneralizeTel con xs = go 0 xs
  where
    infos = map (argInfo . fst) xs
    recSub i = unpackSub con infos i
    go _ [] = EmptyTel
    go i ((name, ty) : xs) = ExtendTel (dom ty') $ Abs (unArg name) $ go (i + 1) xs
      where ty' = applySubst (recSub i) ty
            dom = defaultNamedArgDom (getArgInfo name) (unArg name)

-- | Create metas for all used generalizable variables and their dependencies.
createGenValues :: Set QName -> TCM (Map MetaId QName, Map QName GeneralizedValue)
createGenValues s = do
  genvals <- locallyTC eGeneralizeMetas (const YesGeneralizeVar) $
               mapM createGenValue $ sortBy (compare `on` getRange) $ Set.toList s
  let metaMap = Map.fromListWith __IMPOSSIBLE__ [ (m, x) | (x, m, _) <- genvals ]
      nameMap = Map.fromListWith __IMPOSSIBLE__ [ (x, v) | (x, _, v) <- genvals ]
  return (metaMap, nameMap)

-- | Create a generalisable meta for a generalisable variable.
createGenValue :: QName -> TCM (QName, MetaId, GeneralizedValue)
createGenValue x = setCurrentRange x $ do
  cp  <- viewTC eCurrentCheckpoint
  def <- instantiateDef =<< getConstInfo x
                   -- Only prefix of generalizable arguments (for now?)
  let nGen       = case defArgGeneralizable def of
                     NoGeneralizableArgs     -> 0
                     SomeGeneralizableArgs n -> n
      ty         = defType def
      TelV tel _ = telView' ty
      -- Generalizable variables are never explicit, so if they're given as
      -- explicit we default to hidden.
      hideExplicit arg | visible arg = hide arg
                       | otherwise   = arg
      argTel     = telFromList $ map hideExplicit $ take nGen $ telToList tel

  args <- newTelMeta argTel
  metaType <- piApplyM ty args

  let name     = prettyShow (nameConcrete $ qnameName x)
  (m, term) <- newNamedValueMeta DontRunMetaOccursCheck name CmpLeq metaType

  -- Freeze the meta to prevent named generalizable metas from being
  -- instantiated, and set the quantity of the meta to the declared
  -- quantity of the generalisable variable.
  updateMetaVar m $ \ mv ->
    setQuantity (getQuantity (defArgInfo def)) $
    mv { mvFrozen = Frozen }

  -- Set up names of arg metas
  forM_ (zip3 [1..] (map unArg args) (telToList argTel)) $ \ case
    (i, MetaV m _, Dom{unDom = (x, _)}) -> do
      let suf "_" = show i
          suf ""  = show i
          suf x   = x
      setMetaNameSuggestion m (name ++ "." ++ suf x)
    _ -> return ()  -- eta expanded

  -- Update the ArgInfos for the named meta. The argument metas are
  -- created with the correct ArgInfo.
  setMetaGeneralizableArgInfo m $ hideExplicit (defArgInfo def)

  reportSDoc "tc.generalize" 50 $ vcat
    [ "created metas for generalized variable" <+> prettyTCM x
    , nest 2 $ "top  =" <+> prettyTCM term
    , nest 2 $ "args =" <+> prettyTCM args ]

  case term of
    MetaV{} -> return ()
    _       -> genericDocError =<< ("Cannot generalize over" <+> prettyTCM x <+> "of eta-expandable type") <?>
                                    prettyTCM metaType
  return (x, m, GeneralizedValue{ genvalCheckpoint = cp
                                , genvalTerm       = term
                                , genvalType       = metaType })

-- | Create a not-yet correct record type for the generalized telescope. It's not yet correct since
--   we haven't computed the telescope yet, and we need the record type to do it.
createGenRecordType :: Type -> [MetaId] -> TCM (QName, ConHead, [QName])
createGenRecordType genRecMeta@(El genRecSort _) sortedMetas = do
  current <- currentModule
  let freshQName s = qualify current <$> freshName_ (s :: String)
      mkFieldName  = freshQName . (generalizedFieldName ++) <=< getMetaNameSuggestion
  genRecFields <- mapM (defaultDom <.> mkFieldName) sortedMetas
  genRecName   <- freshQName "GeneralizeTel"
  genRecCon    <- freshQName "mkGeneralizeTel" <&> \ con -> ConHead
                  { conName      = con
                  , conDataRecord= IsRecord CopatternMatching
                  , conInductive = Inductive
                  , conFields    = map argFromDom genRecFields
                  }
  projIx <- succ . size <$> getContext
  inTopContext $ forM_ (zip sortedMetas genRecFields) $ \ (meta, fld) -> do
    fieldTy <- getMetaType meta
    let field = unDom fld
    addConstant' field (getArgInfo fld) field fieldTy $
      let proj = Projection { projProper   = Just genRecName
                            , projOrig     = field
                            , projFromType = defaultArg genRecName
                            , projIndex    = projIx
                            , projLams     = ProjLams [defaultArg "gtel"] } in
      Function { funClauses      = []
               , funCompiled     = Nothing
               , funSplitTree    = Nothing
               , funTreeless     = Nothing
               , funInv          = NotInjective
               , funMutual       = Just []
               , funAbstr        = ConcreteDef
               , funDelayed      = NotDelayed
               , funProjection   = Just proj
               , funFlags        = Set.empty
               , funTerminates   = Just True
               , funExtLam       = Nothing
               , funWith         = Nothing
               , funCovering     = []
               }
  addConstant' (conName genRecCon) defaultArgInfo (conName genRecCon) __DUMMY_TYPE__ $ -- Filled in later
    Constructor { conPars   = 0
                , conArity  = length genRecFields
                , conSrcCon = genRecCon
                , conData   = genRecName
                , conAbstr  = ConcreteDef
                , conInd    = Inductive
                , conComp   = emptyCompKit
                , conProj   = Nothing
                , conForced = []
                , conErased = Nothing
                }
  let dummyTel 0 = EmptyTel
      dummyTel n = ExtendTel (defaultDom __DUMMY_TYPE__) $ Abs "_" $ dummyTel (n - 1)
  addConstant' genRecName defaultArgInfo genRecName (sort genRecSort) $
    Record { recPars         = 0
           , recClause       = Nothing
           , recConHead      = genRecCon
           , recNamedCon     = False
           , recFields       = genRecFields
           , recTel          = dummyTel (length genRecFields) -- Filled in later
           , recMutual       = Just []
           , recEtaEquality' = Inferred YesEta
           , recPatternMatching = CopatternMatching
           , recInduction    = Nothing
           , recAbstr        = ConcreteDef
           , recComp         = emptyCompKit
           }
  reportSDoc "tc.generalize" 20 $ vcat
    [ text "created genRec" <+> prettyList_ (map (text . prettyShow . unDom) genRecFields) ]
  reportSDoc "tc.generalize" 80 $ vcat
    [ text "created genRec" <+> text (prettyShow genRecFields) ]
  -- Solve the genRecMeta
  args <- getContextArgs
  let genRecTy = El genRecSort $ Def genRecName $ map Apply args
  noConstraints $ equalType genRecTy genRecMeta
  return (genRecName, genRecCon, map unDom genRecFields)

-- | Once we have the generalized telescope we can fill in the missing details of the record type.
fillInGenRecordDetails :: QName -> ConHead -> [QName] -> Type -> Telescope -> TCM ()
fillInGenRecordDetails name con fields recTy fieldTel = do
  cxtTel <- fmap hideAndRelParams <$> getContextTelescope
  let fullTel = cxtTel `abstract` fieldTel
  -- Field types
  let mkFieldTypes [] EmptyTel = []
      mkFieldTypes (fld : flds) (ExtendTel ty ftel) =
          abstract cxtTel (El s $ Pi (defaultDom recTy) (Abs "r" $ unDom ty)) :
          mkFieldTypes flds (absApp ftel proj)
        where
          s = mkPiSort (defaultDom recTy) (Abs "r" $ unDom ty)
          proj = Var 0 [Proj ProjSystem fld]
      mkFieldTypes _ _ = __IMPOSSIBLE__
  let fieldTypes = mkFieldTypes fields (raise 1 fieldTel)
  reportSDoc "tc.generalize" 40 $ text "Field types:" <+> inTopContext (nest 2 $ vcat $ map prettyTCM fieldTypes)
  zipWithM_ setType fields fieldTypes
  -- Constructor type
  let conType = fullTel `abstract` raise (size fieldTel) recTy
  reportSDoc "tc.generalize" 40 $ text "Final genRecCon type:" <+> inTopContext (prettyTCM conType)
  setType (conName con) conType
  -- Record telescope: Includes both parameters and fields.
  modifyGlobalDefinition name $ \ r ->
    r { theDef = (theDef r) { recTel = fullTel } }
  where
    setType q ty = modifyGlobalDefinition q $ \ d -> d { defType = ty }

{-# LANGUAGE NondecreasingIndentation #-}

-- | Solving size constraints under hypotheses.
--
-- The size solver proceeds as follows:
--
-- 1. Get size constraints, cluster into connected components.
--
--    All size constraints that mention the same metas go into the same
--    cluster.  Each cluster can be solved by itself.
--
--    Constraints that do not fit our format are ignored.
--    We check whether our computed solution fulfills them as well
--    in the last step.
--
-- 2. Find a joint context for each cluster.
--
--    Each constraint comes with its own typing context, which
--    contains size hypotheses @j : Size< i@.  We need to find a
--    common super context in which all constraints of a cluster live,
--    and raise all constraints to this context.
--
--    There might not be a common super context.  Then we are screwed,
--    since our solver is not ready to deal with such a situation.  We
--    will blatantly refuse to solve this cluster and blame it on the
--    user.
--
-- 3. Convert the joint context into a hypothesis graph.
--
--    This is straightforward.  Each de Bruijn index becomes a
--    rigid variable, each typing assumption @j : Size< i@ becomes an
--    arc.
--
-- 4. Convert the constraints into a constraint graph.
--
--    Here we need to convert @MetaV@s into flexible variables.
--
-- 5. Run the solver
--
-- 6. Convert the solution into meta instantiations.
--
-- 7. Double-check whether the constraints are solved.

-- Opportunities for optimization:
--
-- - NamedRigids has some cost to retrieve variable names
--   just for the sake of debug printing.

module Agda.TypeChecking.SizedTypes.Solve where

import Prelude hiding (null)

import Control.Monad hiding (forM, forM_)
import Control.Monad.Trans.Maybe
import Control.Monad.Reader (asks)

import Data.Foldable (Foldable, foldMap, forM_)
import qualified Data.Foldable as Fold
import Data.Function
import qualified Data.List as List
import Data.Monoid
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Traversable as Trav
import Data.Traversable (Traversable, forM)

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars

import Agda.TypeChecking.Monad as TCM hiding (Offset)
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Free
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Constraints as C

import qualified Agda.TypeChecking.SizedTypes as S
import Agda.TypeChecking.SizedTypes.Syntax as Size
import Agda.TypeChecking.SizedTypes.Utils
import Agda.TypeChecking.SizedTypes.WarshallSolver as Size

import Agda.Utils.Cluster
import Agda.Utils.Either
import Agda.Utils.Except ( MonadError(catchError) )
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.NonemptyList as NeList

import qualified Agda.Utils.List as List

import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty (Pretty, prettyShow)
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.Tuple
import qualified Agda.Utils.VarSet as VarSet

import Agda.Utils.Impossible

type CC = Closure TCM.Constraint

-- | Flag to control the behavior of size solver.
data DefaultToInfty
  = DefaultToInfty      -- ^ Instantiate all unconstrained size variables to ∞.
  | DontDefaultToInfty  -- ^ Leave unconstrained size variables unsolved.
  deriving (Eq, Ord, Show)

-- | Solve size constraints involving hypotheses.

solveSizeConstraints :: DefaultToInfty -> TCM ()
solveSizeConstraints flag =  do

  -- 1. Take out the size constraints normalised.

  cs0 <- mapM (mapClosure normalise) =<< S.takeSizeConstraints
    -- NOTE: this deletes the size constraints from the constraint set!
  unless (null cs0) $
    reportSDoc "tc.size.solve" 40 $ vcat $
      [ text $ "Solving constraints (" ++ show flag ++ ")"
      ] ++ map prettyTCM cs0
  let -- Error for giving up
      cannotSolve :: TCM a
      cannotSolve = typeError . GenericDocError =<<
        vcat ("Cannot solve size constraints" : map prettyTCM cs0)

  -- 2. Cluster the constraints by common size metas.

  -- Get all size metas.
  sizeMetaSet <- Set.fromList . map (\ (x, _t, _tel) -> x) <$> S.getSizeMetas True

  -- Pair each constraint with its list of size metas occurring in it.
  cms <- forM cs0 $ \ cl -> enterClosure cl $ \ c -> do

    -- @allMetas@ does not reduce or instantiate;
    -- this is why we require the size constraints to be normalised.
    return (cl, map metaId . Set.toList $
      sizeMetaSet `Set.intersection` allMetas singleton c)

  -- Now, some constraints may have no metas (clcs), the others have at least one (othercs).
  let classify :: (a, [b]) -> Either a (a, NonemptyList b)
      classify (cl, [])     = Left  cl
      classify (cl, (x:xs)) = Right (cl, x :! xs)
  let (clcs, othercs) = List.mapEither classify cms

  -- We cluster the constraints by their metas.
  let ccs = cluster' othercs

  -- 3. Solve each cluster

  -- Solve the closed constraints, one by one.

  forM_ clcs $ \ c -> () <$ solveSizeConstraints_ flag [c]

  -- Solve the clusters.

  constrainedMetas <- Set.unions <$> do
    forM  (ccs) $ \ (cs :: NonemptyList CC) -> do

      -- Convert each constraint in the cluster to the largest context.
      -- (Keep fingers crossed).

      enterClosure (Fold.maximumBy (compare `on` (length . envContext . clEnv)) cs) $ \ _ -> do
        -- Get all constraints that can be cast to the longest context.
        cs' :: [TCM.Constraint] <- catMaybes <$> do
          mapM (runMaybeT . castConstraintToCurrentContext) $ toList cs

        reportSDoc "tc.size.solve" 20 $ vcat $
          [ "converted size constraints to context: " <+> do
              tel <- getContextTelescope
              inTopContext $ prettyTCM tel
          ] ++ map (nest 2 . prettyTCM) cs'

        -- Solve the converted constraints.
        solveSizeConstraints_ flag =<<  mapM buildClosure cs'

  -- 4. Possibly set remaining metas to infinity.

  -- Andreas, issue 1862: do not default to ∞ always, could be too early.
  when (flag == DefaultToInfty) $ do

    -- let constrainedMetas = Set.fromList $ concat $
    --       for cs0 $ \ Closure{ clValue = ValueCmp _ _ u v } ->
    --         allMetas u ++ allMetas v

    -- Set the unconstrained, open size metas to ∞.
    ms <- S.getSizeMetas False -- do not get interaction metas
    unless (null ms) $ do
      inf <- primSizeInf
      forM_ ms $ \ (m, t, tel) -> do
        unless (m `Set.member` constrainedMetas) $ do
        unlessM (isFrozen m) $ do
        reportSDoc "tc.size.solve" 20 $
          "solution " <+> prettyTCM (MetaV m []) <+>
          " := "      <+> prettyTCM inf
        assignMeta 0 m t (List.downFrom $ size tel) inf

  -- -- Double check.
  -- unless (null cs0 && null ms) $ do
  --   flip catchError (const cannotSolve) $
  --     noConstraints $
  --       forM_ cs0 $ \ cl -> enterClosure cl solveConstraint

  -- 5. Make sure we did not lose any constraints.

  -- This is necessary since we have removed the size constraints.
  forM_ cs0 $ \ cl -> enterClosure cl solveConstraint


-- | TODO: this does not actually work!
--
--   We would like to use a constraint @c@ created in context @Δ@ from module @N@
--   in the current context @Γ@ and current module @M@.
--
--   @Δ@ is module tel @Δ₁@ of @N@ extended by some local bindings @Δ₂@.
--   @Γ@ is the current context.
--   The module parameter substitution from current @M@ to @N@ be
--   @Γ ⊢ σ : Δ₁@.
--
--   If @M == N@, we do not need the parameter substitution.  We try raising.
--
--   We first strengthen @Δ ⊢ c@ to live in @Δ₁@ and obtain @c₁ = strengthen Δ₂ c@.
--   We then transport @c₁@ to @Γ@ and obtain @c₂ = applySubst σ c₁@.
--
--   This works for different modules, but if @M == N@ we should not strengthen
--   and then weaken, because strengthening is a partial operation.
--   We should rather lift the substitution @σ@ by @Δ₂@ and then
--   raise by @Γ₂ - Δ₂@.
--   This "raising" might be a strengthening if @Γ₂@ is shorter than @Δ₂@.
--
--   (TODO: If the module substitution does not exist, because @N@ is not
--   a parent of @M@, we cannot use the constraint, as it has been created
--   in an unrelated context.)

castConstraintToCurrentContext' :: Closure TCM.Constraint -> MaybeT TCM TCM.Constraint
castConstraintToCurrentContext' cl = do
  let modN  = envCurrentModule $ clEnv cl
      delta = envContext $ clEnv cl
  -- The module telescope of the constraint.
  -- The constraint could come from the module telescope of the top level module.
  -- In this case, it does not live in any module!
  -- Thus, getSection can return Nothing.
  delta1 <- liftTCM $ maybe empty (^. secTelescope) <$> getSection modN
  -- The number of locals of the constraint.
  let delta2 = size delta - size delta1
  unless (delta2 >= 0) __IMPOSSIBLE__

  -- The current module M and context Γ.
  modM  <- currentModule
  gamma <- liftTCM $ getContextSize
  -- The current module telescope.
  -- Could also be empty, if we are in the front matter or telescope of the top-level module.
  gamma1 <-liftTCM $ maybe empty (^. secTelescope) <$> getSection modM
  -- The current locals.
  let gamma2 = gamma - size gamma1

  -- Γ ⊢ σ : Δ₁
  sigma <- liftTCM $ getModuleParameterSub modN

  -- Debug printing.
  reportSDoc "tc.constr.cast" 40 $ "casting constraint" $$ do
    tel <- getContextTelescope
    inTopContext $ nest 2 $ vcat $
      [ "current module                = " <+> prettyTCM modM
      , "current module telescope      = " <+> prettyTCM gamma1
      , "current context               = " <+> prettyTCM tel
      , "constraint module             = " <+> prettyTCM modN
      , "constraint module telescope   = " <+> prettyTCM delta1
      , "constraint context            = " <+> (prettyTCM =<< enterClosure cl (const $ getContextTelescope))
      , "constraint                    = " <+> enterClosure cl prettyTCM
      , "module parameter substitution = " <+> prettyTCM sigma
      ]

  -- If gamma2 < 0, we must be in the wrong context.
  -- E.g. we could have switched to the empty context even though
  -- we are still inside a module with parameters.
  -- In this case, we cannot safely convert the constraint,
  -- since the module parameter substitution may be wrong.
  guard (gamma2 >= 0)

  -- Shortcut for modN == modM:
  -- Raise constraint from Δ to Γ, if possible.
  -- This might save us some strengthening.
  if modN == modM then raiseMaybe (gamma - size delta) $ clValue cl else do

  -- Strengthen constraint to Δ₁ ⊢ c
  c <- raiseMaybe (-delta2) $ clValue cl

  -- Ulf, 2016-11-09: I don't understand what this function does when M and N
  -- are not related. Certainly things can go terribly wrong (see
  -- test/Succeed/Issue2223b.agda)
  fv <- liftTCM $ getModuleFreeVars modN
  guard $ fv == size delta1

  -- Γ ⊢ c[σ]
  return $ applySubst sigma c
  where
    raiseMaybe n c = do
      -- Fine if we have to weaken or strengthening is safe.
      guard $ n >= 0 || List.all (>= -n) (VarSet.toList $ allFreeVars c)
      return $ raise n c


-- | A hazardous hack, may the Gods have mercy on us.
--
--   To cast to the current context, we match the context of the
--   given constraint by 'CtxId', and as fallback, by variable name (douh!).
--
--   This hack lets issue 2046 go through.

castConstraintToCurrentContext :: Closure TCM.Constraint -> MaybeT TCM TCM.Constraint
castConstraintToCurrentContext cl = do
  -- The checkpoint of the contraint
  let cp = envCurrentCheckpoint $ clEnv cl
  sigma <- caseMaybeM (viewTC $ eCheckpoints . key cp)
          (do
            -- We are not in a descendant of the constraint checkpoint.
            -- Here be dragons!!
            gamma <- asksTC envContext -- The target context
            let findInGamma (Dom {unDom = (x, t)}) =
                  -- match by name (hazardous)
                  -- This is one of the seven deadly sins (not respecting alpha).
                  List.findIndex ((x ==) . fst . unDom) gamma
            let delta = envContext $ clEnv cl
                cand  = map findInGamma delta
            -- The domain of our substitution
            let coveredVars = VarSet.fromList $ catMaybes $ zipWith ($>) cand [0..]
            -- Check that all the free variables of the constraint are contained in
            -- coveredVars.
            -- We ignore the free variables occurring in sorts.
            guard $ getAll $ runFree (All . (`VarSet.member` coveredVars)) IgnoreAll (clValue cl)
            -- Turn cand into a substitution.
            -- Since we ignored the free variables in sorts, we better patch up
            -- the substitution with some dummy term rather than __IMPOSSIBLE__.
            return $ parallelS $ map (maybe __DUMMY_TERM__ var) cand
          ) return -- Phew, we've got the checkpoint! All is well.
  -- Apply substitution to constraint and pray that the Gods are merciful on us.
  return $ applySubst sigma (clValue cl)
  -- Note: the resulting constraint may not well-typed.
  -- Even if it is, it may map variables to their wrong counterpart.

-- | Return the size metas occurring in the simplified constraints.
--   A constraint like @↑ _j =< ∞ : Size@ simplifies to nothing,
--   so @_j@ would not be in this set.
solveSizeConstraints_ :: DefaultToInfty -> [CC] -> TCM (Set MetaId)
solveSizeConstraints_ flag cs0 = do
  -- Pair constraints with their representation as size constraints.
  -- Discard constraints that do not have such a representation.
  ccs :: [(CC,HypSizeConstraint)] <- catMaybes <$> do
    forM cs0 $ \ c0 -> fmap (c0,) <$> computeSizeConstraint c0

  -- Simplify constraints and check for obvious inconsistencies.
  ccs' <- concat <$> do
    forM ccs $ \ (c0, HypSizeConstraint cxt hids hs sc) -> do
      case simplify1 (\ sc -> return [sc]) sc of
        Left _ -> typeError . GenericDocError =<< do
          "Contradictory size constraint" <+> prettyTCM c0
        Right cs -> return $ (c0,) . HypSizeConstraint cxt hids hs <$> cs

  -- Cluster constraints according to the meta variables they mention.
  -- @csNoM@ are the constraints that do not mention any meta.
  let (csNoM, csMs) = (`List.partitionMaybe` ccs') $ \ p@(c0, c) ->
        fmap (p,) $ NeList.fromList $ map (metaId . sizeMetaId) $ Set.toList $ flexs c
  -- @css@ are the clusters of constraints.
      css :: [NonemptyList (CC,HypSizeConstraint)]
      css = cluster' csMs

  -- Check that the closed constraints are valid.
  whenJust (NeList.fromList csNoM) $ solveCluster flag

  -- Now, process the clusters.
  forM_ css $ solveCluster flag

  return $ Set.mapMonotonic sizeMetaId $ flexs $ map (snd . fst) csMs

-- | Solve a cluster of constraints sharing some metas.
--
solveCluster :: DefaultToInfty -> NonemptyList (CC,HypSizeConstraint) -> TCM ()
solveCluster flag ccs = do
  let cs = fmap snd ccs
  let prettyCs   = map prettyTCM $ NeList.toList cs
  let err reason = typeError . GenericDocError =<< do
        vcat $
          [ text $ "Cannot solve size constraints" ] ++ prettyCs ++
          [ text $ "Reason: " ++ reason ]
  reportSDoc "tc.size.solve" 20 $ vcat $
    [ "Solving constraint cluster" ] ++ prettyCs
  -- Find the super context of all contexts.
{-
  -- We use the @'ctxId'@s.
  let cis@(ci:cis') = for cs $ \ c -> (c, reverse $ map ctxId $ sizeContext c)
--  let cis@(ci:cis') = for cs $ \ c -> (c, reverse $ sizeHypIds c)
      max a@Left{}            _            = a
      max a@(Right ci@(c,is)) ci'@(c',is') =
        case preOrSuffix is is' of
          -- No common context:
          IsNofix    -> Left (ci, ci')
          IsPrefix{} -> Right ci'
          _          -> a
      res = foldl' max (Right ci) cis'
      noContext ((c,is),(c',is')) = typeError . GenericDocError =<< vcat
        [ "Cannot solve size constraints; the following constraints have no common typing context:"
        , prettyTCM c
        , prettyTCM c'
        ]
  flip (either noContext) res $ \ (HypSizeConstraint gamma hids hs _, _) -> do
-}
  -- We rely on the fact that contexts are only extended...
  -- Just take the longest context.
  let HypSizeConstraint gamma hids hs _ = Fold.maximumBy (compare `on` (length . sizeContext)) cs
  -- Length of longest context.
  let n = size gamma

  -- Now convert all size constraints to the largest context.
      csL = for cs $ \ (HypSizeConstraint cxt _ _ c) -> raise (n - size cxt) c
  -- Canonicalize the constraints.
  -- This is unsound in the presence of hypotheses.
      csC :: [SizeConstraint]
      csC = applyWhen (null hs) (mapMaybe canonicalizeSizeConstraint) $ NeList.toList csL
  reportSDoc "tc.size.solve" 30 $ vcat $
    [ "Size hypotheses" ] ++
    map (prettyTCM . HypSizeConstraint gamma hids hs) hs ++
    [ "Canonicalized constraints" ] ++
    map (prettyTCM . HypSizeConstraint gamma hids hs) csC

  -- -- ALT:
  -- -- Now convert all size constraints to de Bruijn levels.

  -- -- To get from indices in a context of length m <= n
  -- -- to levels into the target context of length n,
  -- -- we apply the following substitution:
  -- -- Index m-1 needs to be mapped to level 0,
  -- -- index m-2 needs to be mapped to level 1,
  -- -- index 0 needs to be mapped to level m-1,
  -- -- so the desired substitution is @downFrom m@.
  -- let sub m = applySubst $ parallelS $ map var $ downFrom m

  -- -- We simply reverse the context to get to de Bruijn levels.
  -- -- Of course, all types in the context are broken, but
  -- -- only need it for pretty printing constraints.
  -- gamma <- return $ reverse gamma

  -- -- We convert the hypotheses to de Bruijn levels.
  -- hs <- return $ sub n hs

  -- -- We get a form for pretty-printing
  -- let prettyC = prettyTCM . HypSizeConstraint gamma hids hs

  -- -- We convert the constraints to de Bruijn level format.
  -- let csC :: [SizeConstraint]
  --     csC = for cs $ \ (HypSizeConstraint cxt _ _ c) -> sub (size cxt) c

  -- reportSDoc "tc.size.solve" 30 $ vcat $
  --   [ "Size hypotheses" ]           ++ map prettyC hs ++
  --   [ "Canonicalized constraints" ] ++ map prettyC csC

  -- Convert size metas to flexible vars.
  let metas :: [SizeMeta]
      metas = concat $ map (foldMap (:[])) csC
      csF   :: [Size.Constraint' NamedRigid Int]
      csF   = map (fmap (metaId . sizeMetaId)) csC

  -- Construct the hypotheses graph.
  let hyps = map (fmap (metaId . sizeMetaId)) hs
  -- There cannot be negative cycles in hypotheses graph due to scoping.
  let hg = fromRight __IMPOSSIBLE__ $ hypGraph (rigids csF) hyps

  -- -- Construct the constraint graph.
  -- --    g :: Size.Graph NamedRigid Int Label
  -- g <- either err return $ constraintGraph csF hg
  -- reportSDoc "tc.size.solve" 40 $ vcat $
  --   [ "Constraint graph"
  --   , text (show g)
  --   ]

  -- sol :: Solution NamedRigid Int <- either err return $ solveGraph Map.empty hg g
  -- either err return $ verifySolution hg csF sol

  -- Andreas, 2016-07-13, issue 2096.
  -- Running the solver once might result in unsolvable left-over constraints.
  -- We need to iterate the solver to detect this.
  sol :: Solution NamedRigid Int <- either err return $
    iterateSolver Map.empty hg csF emptySolution

  -- Convert solution to meta instantiation.
  solved <- fmap Set.unions $ forM (Map.assocs $ theSolution sol) $ \ (m, a) -> do
    unless (validOffset a) __IMPOSSIBLE__
    -- Solution does not contain metas
    u <- unSizeExpr $ fmap __IMPOSSIBLE__ a
    let x = MetaId m
    let SizeMeta _ xs = fromMaybe __IMPOSSIBLE__ $
          List.find ((m==) . metaId . sizeMetaId) metas
    -- Check that solution is well-scoped
    let ys = rigidIndex <$> Set.toList (rigids a)
        ok = all (`elem` xs) ys -- TODO: more efficient
    -- unless ok $ err "ill-scoped solution for size meta variable"
    u <- if ok then return u else primSizeInf
    t <- getMetaType x
    reportSDoc "tc.size.solve" 20 $ inTopContext $ modifyContext (const gamma) $ do
      let args = map (Apply . defaultArg . var) xs
      "solution " <+> prettyTCM (MetaV x args) <+> " := " <+> prettyTCM u
    reportSDoc "tc.size.solve" 60 $ vcat
      [ text $ "  xs = " ++ show xs
      , text $ "  u  = " ++ show u
      ]
    ifM (isFrozen x `or2M` (not <$> asksTC envAssignMetas)) (return Set.empty) $ do
      assignMeta n x t xs u
      return $ Set.singleton x
    -- WRONG:
    -- let partialSubst = List.sort $ zip xs $ map var $ downFrom n
    -- assignMeta' n x t (length xs) partialSubst u
    -- WRONG: assign DirEq x (map (defaultArg . var) xs) u

  -- Possibly set remaining size metas to ∞ (issue 1862)
  -- unless we have an interaction meta in the cluster (issue 2095).

  ims <- Set.fromList <$> getInteractionMetas

  --  ms = unsolved size metas from cluster
  let ms = Set.fromList (map sizeMetaId metas) Set.\\ solved
  --  Make sure they do not contain an interaction point
  let noIP = Set.null $ Set.intersection ims ms

  unless (null ms) $ reportSDoc "tc.size.solve" 30 $ fsep $
    [ "cluster did not solve these size metas: " ] ++ map prettyTCM (Set.toList ms)

  solvedAll <- do
    -- If no metas are left, we have solved this cluster completely.
    if Set.null ms                then return True  else do
    -- Otherwise, we can solve it completely if we are allowed to set to ∞.
    if flag == DontDefaultToInfty then return False else do
    -- Which is only the case when we have no interaction points in the cluster.
    if not noIP                   then return False else do
    -- Try to set all unconstrained size metas to ∞.
    inf <- primSizeInf
    and <$> do
      forM (Set.toList ms) $ \ m -> do
        -- If one variable is frozen, we cannot set it (and hence not all) to ∞
        let no = do
              reportSDoc "tc.size.solve" 30 $
                prettyTCM (MetaV m []) <+> "is frozen, cannot set it to ∞"
              return False
        ifM (isFrozen m `or2M` do not <$> asksTC envAssignMetas) no $ {-else-} do
          reportSDoc "tc.size.solve" 20 $
            "solution " <+> prettyTCM (MetaV m []) <+>
            " := "      <+> prettyTCM inf
          t <- jMetaType . mvJudgement <$> lookupMeta m
          TelV tel core <- telView t
          unlessM (isJust <$> isSizeType core) __IMPOSSIBLE__
          assignMeta 0 m t (List.downFrom $ size tel) inf
          return True

  -- Double check.
  when solvedAll $ do
    let cs0 = map fst $ toList ccs
        -- Error for giving up
        cannotSolve = typeError . GenericDocError =<<
          vcat ("Cannot solve size constraints" : map prettyTCM cs0)
    flip catchError (const cannotSolve) $
      noConstraints $
        forM_ cs0 $ \ cl -> enterClosure cl solveConstraint

-- | Collect constraints from a typing context, looking for SIZELT hypotheses.
getSizeHypotheses :: Context -> TCM [(Nat, SizeConstraint)]
getSizeHypotheses gamma = inTopContext $ modifyContext (const gamma) $ do
  (_, msizelt) <- getBuiltinSize
  caseMaybe msizelt (return []) $ \ sizelt -> do
    -- Traverse the context from newest to oldest de Bruijn Index
    catMaybes <$> do
      forM (zip [0..] gamma) $ \ (i, ce) -> do
        -- Get name and type of variable i.
        let (x, t) = unDom ce
            s      = prettyShow x
        t <- reduce . raise (1 + i) . unEl $ t
        case t of
          Def d [Apply u] | d == sizelt -> do
            caseMaybeM (sizeExpr $ unArg u) (return Nothing) $ \ a ->
              return $ Just $ (i, Constraint (Rigid (NamedRigid s i) 0) Lt a)
          _ -> return Nothing

-- | Convert size constraint into form where each meta is applied
--   to indices @n-1,...,1,0@ where @n@ is the arity of that meta.
--
--   @X[σ] <= t@ becomes @X[id] <= t[σ^-1]@
--
--   @X[σ] ≤ Y[τ]@ becomes @X[id] ≤ Y[τ[σ^-1]]@ or @X[σ[τ^1]] ≤ Y[id]@
--   whichever is defined.  If none is defined, we give up.
--
--   Cf. @SizedTypes.oldCanonicalizeSizeConstraint@.
--
--   Fixes (the rather artificial) issue 300.
--   But it is unsound when pruned metas occur and triggers issue 1914.
--   Thus we deactivate it.
--   This needs to be properly implemented, possibly using the
--   metaPermuatation of each meta variable.

canonicalizeSizeConstraint :: SizeConstraint -> Maybe (SizeConstraint)
canonicalizeSizeConstraint c@(Constraint a cmp b) = Just c
{-
  case (a,b) of

    -- Case flex-flex
    (Flex (SizeMeta m xs) n, Flex (SizeMeta l ys) n')
         -- try to invert xs on ys
       | let len = size xs
       , Just ys' <- mapM (\ y -> (len-1 -) <$> findIndex (==y) xs) ys ->
           return $ Constraint (Flex (SizeMeta m $ downFrom len) n)
                           cmp (Flex (SizeMeta l ys') n')
         -- try to invert ys on xs
       | let len = size ys
       , Just xs' <- mapM (\ x -> (len-1 -) <$> findIndex (==x) ys) xs ->
           return $ Constraint (Flex (SizeMeta m xs') n)
                           cmp (Flex (SizeMeta l $ downFrom len) n')
         -- give up
       | otherwise -> Nothing

    -- Case flex-rigid
    (Flex (SizeMeta m xs) n, Rigid (NamedRigid x i) n') -> do
      let len = size xs
      j <- (len-1 -) <$> findIndex (==i) xs
      return $ Constraint (Flex (SizeMeta m $ downFrom len) n)
                      cmp (Rigid (NamedRigid x j) n')

    -- Case rigid-flex
    (Rigid (NamedRigid x i) n, Flex (SizeMeta m xs) n') -> do
      let len = size xs
      j <- (len-1 -) <$> findIndex (==i) xs
      return $ Constraint (Rigid (NamedRigid x j) n)
                      cmp (Flex (SizeMeta m $ downFrom len) n')

    -- Case flex-const
    (Flex (SizeMeta m xs) n, _)      ->
      return $ Constraint (Flex (SizeMeta m $ downFrom $ size xs) n) cmp b

    -- Case const-flex
    (_, Flex (SizeMeta m xs) n') -> do
      return $ Constraint a cmp (Flex (SizeMeta m $ downFrom $ size xs) n')

    -- Case no flex
    _ -> return c
-}

-- | Identifiers for rigid variables.
data NamedRigid = NamedRigid
  { rigidName  :: String   -- ^ Name for printing in debug messages.
  , rigidIndex :: Int      -- ^ De Bruijn index.
  } deriving (Show)

instance Eq NamedRigid where (==) = (==) `on` rigidIndex
instance Ord NamedRigid where compare = compare `on` rigidIndex
instance Pretty NamedRigid where pretty = P.text . rigidName
instance Plus NamedRigid Int NamedRigid where
  plus (NamedRigid x i) j = NamedRigid x (i + j)

-- | Size metas in size expressions.
data SizeMeta = SizeMeta
  { sizeMetaId   :: MetaId
  -- TODO to fix issue 300?
  -- , sizeMetaPerm :: Permutation -- ^ Permutation from the current context
  --                               --   to the context of the meta.
  , sizeMetaArgs :: [Int]       -- ^ De Bruijn indices.
  } deriving (Show)

-- | An equality which ignores the meta arguments.
instance Eq  SizeMeta where (==)    = (==)    `on` sizeMetaId
-- | An order which ignores the meta arguments.
instance Ord SizeMeta where compare = compare `on` sizeMetaId

instance Pretty SizeMeta where pretty = P.pretty . sizeMetaId

instance PrettyTCM SizeMeta where
  prettyTCM (SizeMeta x es) = prettyTCM (MetaV x $ map (Apply . defaultArg . var) es)

instance Subst Term SizeMeta where
  applySubst sigma (SizeMeta x es) = SizeMeta x (map raise es)
    where
      raise i =
        case lookupS sigma i of
          Var j [] -> j
          _        -> __IMPOSSIBLE__

-- | Size expression with de Bruijn indices.
type DBSizeExpr = SizeExpr' NamedRigid SizeMeta

-- deriving instance Functor     (SizeExpr' Int)
-- deriving instance Foldable    (SizeExpr' Int)
-- deriving instance Traversable (SizeExpr' Int)

-- | Only for 'raise'.
instance Subst Term (SizeExpr' NamedRigid SizeMeta) where
  applySubst sigma a =
    case a of
      Infty   -> a
      Const{} -> a
      Flex  x n -> Flex (applySubst sigma x) n
      Rigid r n ->
        case lookupS sigma $ rigidIndex r of
          Var j [] -> Rigid r{ rigidIndex = j } n
          _        -> __IMPOSSIBLE__

type SizeConstraint = Constraint' NamedRigid SizeMeta

instance Subst Term SizeConstraint where
  applySubst sigma (Constraint a cmp b) =
    Constraint (applySubst sigma a) cmp (applySubst sigma b)

-- | Assumes we are in the right context.
instance PrettyTCM (SizeConstraint) where
  prettyTCM (Constraint a cmp b) = do
    u <- unSizeExpr a
    v <- unSizeExpr b
    prettyTCM u <+> pretty cmp <+> prettyTCM v

-- | Size constraint with de Bruijn indices.
data HypSizeConstraint = HypSizeConstraint
  { sizeContext    :: Context
  , sizeHypIds     :: [Nat] -- ^ DeBruijn indices
  , sizeHypotheses :: [SizeConstraint]  -- ^ Living in @Context@.
  , sizeConstraint :: SizeConstraint    -- ^ Living in @Context@.
  }

instance Flexs SizeMeta HypSizeConstraint where
  flexs (HypSizeConstraint _ _ hs c) = flexs hs `mappend` flexs c

instance PrettyTCM HypSizeConstraint where
  prettyTCM (HypSizeConstraint cxt _ hs c) =
    inTopContext $ modifyContext (const cxt) $ do
      let cxtNames = reverse $ map (fst . unDom) cxt
      -- text ("[#cxt=" ++ show (size cxt) ++ "]") <+> do
      prettyList (map prettyTCM cxtNames) <+> do
      applyUnless (null hs)
       (((hcat $ punctuate ", " $ map prettyTCM hs) <+> "|-") <+>)
       (prettyTCM c)

-- | Turn a constraint over de Bruijn indices into a size constraint.
computeSizeConstraint :: Closure TCM.Constraint -> TCM (Maybe HypSizeConstraint)
computeSizeConstraint c = do
  let cxt = envContext $ clEnv c
  inTopContext $ modifyContext (const cxt) $ do
    case clValue c of
      ValueCmp CmpLeq _ u v -> do
        reportSDoc "tc.size.solve" 50 $ sep $
          [ "converting size constraint"
          , prettyTCM c
          ]
        ma <- sizeExpr u
        mb <- sizeExpr v
        (hids, hs) <- unzip <$> getSizeHypotheses cxt
        let mk a b = HypSizeConstraint cxt hids hs $ Size.Constraint a Le b
        -- We only create a size constraint if both terms can be
        -- parsed to our format of size expressions.
        return $ mk <$> ma <*> mb
      _ -> __IMPOSSIBLE__

-- | Turn a term into a size expression.
--
--   Returns 'Nothing' if the term isn't a proper size expression.

sizeExpr :: Term -> TCM (Maybe DBSizeExpr)
sizeExpr u = do
  u <- reduce u -- Andreas, 2009-02-09.
                -- This is necessary to surface the solutions of metavariables.
  reportSDoc "tc.conv.size" 60 $ "sizeExpr:" <+> prettyTCM u
  s <- sizeView u
  case s of
    SizeInf     -> return $ Just Infty
    SizeSuc u   -> fmap (`plus` (1 :: Offset)) <$> sizeExpr u
    OtherSize u -> case u of
      Var i []    -> (\ x -> Just $ Rigid (NamedRigid x i) 0) . prettyShow <$> nameOfBV i
--      MetaV m es  -> return $ Just $ Flex (SizeMeta m es) 0
      MetaV m es | Just xs <- mapM isVar es, List.fastDistinct xs
                  -> return $ Just $ Flex (SizeMeta m xs) 0
      _           -> return Nothing
  where
    isVar (Proj{})  = Nothing
    isVar (IApply _ _ v) = isVar (Apply (defaultArg v))
    isVar (Apply v) = case unArg v of
      Var i [] -> Just i
      _        -> Nothing

-- | Turn a de size expression into a term.
unSizeExpr :: HasBuiltins m => DBSizeExpr -> m Term
unSizeExpr a =
  case a of
    Infty         -> fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinSizeInf
    Rigid r (O n) -> do
      unless (n >= 0) __IMPOSSIBLE__
      sizeSuc n $ var $ rigidIndex r
    Flex (SizeMeta x es) (O n) -> do
      unless (n >= 0) __IMPOSSIBLE__
      sizeSuc n $ MetaV x $ map (Apply . defaultArg . var) es
    Const{} -> __IMPOSSIBLE__

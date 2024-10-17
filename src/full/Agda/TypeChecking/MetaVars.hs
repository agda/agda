{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.MetaVars where

import Prelude hiding (null)

import Control.Monad.Except ( MonadError(..), ExceptT, runExceptT )
import Control.Monad.Trans.Maybe

import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import qualified Data.Map.Strict as MapS
import qualified Data.Set as Set
import qualified Data.Foldable as Fold
import qualified Data.Traversable as Trav

import Agda.Interaction.Options

import Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Common
import Agda.Syntax.Info ( MetaKind( InstanceMeta, UnificationMeta ), MetaNameSuggestion)
import qualified Agda.Syntax.Info as A
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic
import Agda.Syntax.Internal.MetaVars
import Agda.Syntax.Position (getRange, killRange)

import Agda.TypeChecking.Monad
-- import Agda.TypeChecking.Monad.Builtin
-- import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Sort
import Agda.TypeChecking.Substitute
import qualified Agda.TypeChecking.SyntacticEquality as SynEq
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Free
import Agda.TypeChecking.Lock
import Agda.TypeChecking.Level (levelType)
import Agda.TypeChecking.Records
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.SizedTypes (boundedSizeMetaHook, isSizeProblem)
import {-# SOURCE #-} Agda.TypeChecking.CheckInternal
import {-# SOURCE #-} Agda.TypeChecking.Conversion

-- import Agda.TypeChecking.CheckInternal
-- import {-# SOURCE #-} Agda.TypeChecking.CheckInternal (checkInternal)
import Agda.TypeChecking.MetaVars.Occurs

import qualified Agda.Utils.BiMap as BiMap
import Agda.Utils.Function
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.List1 (List1, pattern (:|))
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Tuple
import Agda.Utils.Permutation
import Agda.Syntax.Common.Pretty (Pretty, prettyShow, render)
import qualified Agda.Utils.ProfileOptions as Profile
import Agda.Utils.Singleton
import qualified Agda.Utils.Graph.TopSort as Graph
import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as VarSet

import Agda.Utils.Impossible

instance MonadMetaSolver TCM where
  newMeta' = newMetaTCM'
  assignV dir x args v t = assignWrapper dir x (map Apply args) v $ assign dir x args v t
  assignTerm' = assignTermTCM'
  etaExpandMeta = etaExpandMetaTCM
  updateMetaVar = updateMetaVarTCM

  -- Right now we roll back the full state when aborting.
  -- TODO: only roll back the metavariables
  speculateMetas fallback m = do
    (a, s) <- localTCStateSaving m
    case a of
      KeepMetas     -> putTC s
      RollBackMetas -> fallback

-- | Find position of a value in a list.
--   Used to change metavar argument indices during assignment.
--
--   @reverse@ is necessary because we are directly abstracting over the list.
--
findIdx :: Eq a => [a] -> a -> Maybe Int
findIdx vs v = List.elemIndex v (reverse vs)

-- | Does the given local meta-variable have a twin meta-variable?

hasTwinMeta :: MetaId -> TCM Bool
hasTwinMeta x = do
    m <- lookupLocalMeta x
    return $ isJust $ mvTwin m

-- | Check whether a meta variable is a place holder for a blocked term.
isBlockedTerm :: MetaId -> TCM Bool
isBlockedTerm x = do
    reportSLn "tc.meta.blocked" 12 $ "is " ++ prettyShow x ++ " a blocked term? "
    i <- lookupMetaInstantiation x
    let r = case i of
            BlockedConst{}                 -> True
            PostponedTypeCheckingProblem{} -> True
            InstV{}                        -> False
            OpenMeta{}                     -> False
    reportSLn "tc.meta.blocked" 12 $
      if r then "  yes, because " ++ prettyShow i else "  no"
    return r

isEtaExpandable :: [MetaClass] -> MetaId -> TCM Bool
isEtaExpandable classes x = do
    i <- lookupMetaInstantiation x
    return $ case i of
      OpenMeta UnificationMeta       -> True
      OpenMeta InstanceMeta          -> Records `notElem` classes
      InstV{}                        -> False
      BlockedConst{}                 -> False
      PostponedTypeCheckingProblem{} -> False

-- * Performing the assignment

-- | Performing the meta variable assignment.
--
--   The instantiation should not be an 'InstV' and the 'MetaId'
--   should point to something 'Open' or a 'BlockedConst'.
--   Further, the meta variable may not be 'Frozen'.
assignTerm :: MonadMetaSolver m => MetaId -> [Arg ArgName] -> Term -> m ()
assignTerm x tel v = do
     -- verify (new) invariants
    whenM (isFrozen x) __IMPOSSIBLE__
    assignTerm' x tel v

-- | Skip frozen check.  Used for eta expanding frozen metas.
assignTermTCM' :: MetaId -> [Arg ArgName] -> Term -> TCM ()
assignTermTCM' x tel v = do
    reportSDoc "tc.meta.assign" 70 $ vcat
      [ "assignTerm" <+> prettyTCM x <+> " := " <+> prettyTCM v
      , nest 2 $ "tel =" <+> prettyList_ (map (text . unArg) tel)
      ]
     -- verify (new) invariants
    whenM (not <$> asksTC envAssignMetas) __IMPOSSIBLE__

    whenProfile Profile.Metas $ liftTCM $ return () {-tickMax "max-open-metas" . (fromIntegral . size) =<< getOpenMetas-}
    updateMetaVarTCM x $ \ mv ->
      mv { mvInstantiation = InstV $ Instantiation
             { instTel = tel
             , instBody = v
             -- Andreas, 2022-04-28, issue #5875:
             -- Can't killRange the meta-solution, since this will destroy
             -- ranges of termination errors (and potentially other passes
             -- that run on internal syntax)!
             -- , instBody = killRange v
             }
         }
    etaExpandListeners x
    wakeupConstraints x
    reportSLn "tc.meta.assign" 20 $ "completed assignment of " ++ prettyShow x

-- * Creating meta variables.

-- | Create a sort meta that cannot be instantiated with 'Inf' (Setω).
newSortMetaBelowInf :: TCM Sort
newSortMetaBelowInf = do
  x <- newSortMeta
  hasBiggerSort x
  return x

{-# SPECIALIZE newSortMeta :: TCM Sort #-}
-- | Create a sort meta that may be instantiated with 'Inf' (Setω).
newSortMeta :: MonadMetaSolver m => m Sort
newSortMeta =
  ifM hasUniversePolymorphism (newSortMetaCtx =<< getContextArgs)
  -- else (no universe polymorphism)
  $ do i   <- createMetaInfo
       let j = IsSort () __DUMMY_TYPE__
       x   <- newMeta Instantiable i normalMetaPriority (idP 0) j
       reportSDoc "tc.meta.new" 50 $
         "new sort meta" <+> prettyTCM x
       return $ MetaS x []

-- | Create a sort meta that may be instantiated with 'Inf' (Setω).
newSortMetaCtx :: MonadMetaSolver m => Args -> m Sort
newSortMetaCtx vs = do
    i   <- createMetaInfo
    tel <- getContextTelescope
    let t = telePi_ tel __DUMMY_TYPE__
    x   <- newMeta Instantiable i normalMetaPriority (idP $ size tel) $ IsSort () t
    reportSDoc "tc.meta.new" 50 $
      "new sort meta" <+> prettyTCM x <+> ":" <+> prettyTCM t
    return $ MetaS x $ map Apply vs

newTypeMeta' :: Comparison -> Sort -> TCM Type
newTypeMeta' cmp s = El s . snd <$> newValueMeta RunMetaOccursCheck cmp (sort s)

newTypeMeta :: Sort -> TCM Type
newTypeMeta = newTypeMeta' CmpLeq

newTypeMeta_ ::  TCM Type
newTypeMeta_  = newTypeMeta' CmpEq =<< (workOnTypes $ newSortMeta)
-- TODO: (this could be made work with new uni-poly)
-- Andreas, 2011-04-27: If a type meta gets solved, than we do not have to check
-- that it has a sort.  The sort comes from the solution.
-- newTypeMeta_  = newTypeMeta Inf

{-# SPECIALIZE newLevelMeta :: TCM Level #-}
newLevelMeta :: MonadMetaSolver m => m Level
newLevelMeta = do
  (x, v) <- newValueMeta RunMetaOccursCheck CmpEq =<< levelType
  return $ case v of
    Level l    -> l
    _          -> atomicLevel v

{-# SPECIALIZE newInstanceMeta :: MetaNameSuggestion -> Type -> TCM (MetaId, Term) #-}
-- | @newInstanceMeta s t cands@ creates a new instance metavariable
--   of type the output type of @t@ with name suggestion @s@.
newInstanceMeta
  :: MonadMetaSolver m
  => MetaNameSuggestion -> Type -> m (MetaId, Term)
newInstanceMeta s t = do
  vs  <- getContextArgs
  ctx <- getContextTelescope
  newInstanceMetaCtx s (telePi_ ctx t) vs

newInstanceMetaCtx
  :: MonadMetaSolver m
  => MetaNameSuggestion -> Type -> Args -> m (MetaId, Term)
newInstanceMetaCtx s t vs = do
  reportSDoc "tc.meta.new" 50 $ fsep
    [ "new instance meta:"
    , nest 2 $ prettyTCM vs <+> "|-"
    ]
  -- Andreas, 2017-10-04, issue #2753: no metaOccurs check for instance metas
  i0 <- createMetaInfo' DontRunMetaOccursCheck
  let i = i0 { miNameSuggestion = s }
  TelV tel _ <- telView t
  let perm = idP (size tel)
  x <- newMeta' (OpenMeta InstanceMeta) Instantiable i normalMetaPriority perm (HasType () CmpLeq t)
  reportSDoc "tc.meta.new" 50 $ fsep
    [ nest 2 $ pretty x <+> ":" <+> prettyTCM t
    ]
  let c = FindInstance x Nothing
  addAwakeConstraint alwaysUnblock c
  etaExpandMetaSafe x
  return (x, MetaV x $ map Apply vs)

-- | Create a new value meta with specific dependencies, possibly η-expanding in the process.
newNamedValueMeta :: MonadMetaSolver m => RunMetaOccursCheck -> MetaNameSuggestion -> Comparison -> Type -> m (MetaId, Term)
newNamedValueMeta b s cmp t = do
  (x, v) <- newValueMeta b cmp t
  setMetaNameSuggestion x s
  return (x, v)

-- | Create a new value meta with specific dependencies without η-expanding.
newNamedValueMeta' :: MonadMetaSolver m => RunMetaOccursCheck -> MetaNameSuggestion -> Comparison -> Type -> m (MetaId, Term)
newNamedValueMeta' b s cmp t = do
  (x, v) <- newValueMeta' b cmp t
  setMetaNameSuggestion x s
  return (x, v)

{-# SPECIALIZE newValueMetaOfKind :: A.MetaInfo -> RunMetaOccursCheck -> Comparison -> Type -> TCM (MetaId, Term) #-}
newValueMetaOfKind :: MonadMetaSolver m
  => A.MetaInfo
  -> RunMetaOccursCheck  -- ^ Ignored for instance metas.
  -> Comparison          -- ^ Ignored for instance metas.
  -> Type
  -> m (MetaId, Term)
newValueMetaOfKind info = case A.metaKind info of
  UnificationMeta -> newValueMeta
  InstanceMeta -> \ _run _cmp -> newInstanceMeta (A.metaNameSuggestion info)

{-# SPECIALIZE newValueMeta :: RunMetaOccursCheck -> Comparison -> Type -> TCM (MetaId, Term) #-}
-- | Create a new metavariable, possibly η-expanding in the process.
newValueMeta :: MonadMetaSolver m => RunMetaOccursCheck -> Comparison -> Type -> m (MetaId, Term)
newValueMeta b cmp t = do
  vs  <- getContextArgs
  tel <- getContextTelescope
  newValueMetaCtx Instantiable b cmp t tel (idP $ size tel) vs

newValueMetaCtx
  :: MonadMetaSolver m
  => Frozen -> RunMetaOccursCheck -> Comparison -> Type -> Telescope -> Permutation -> Args -> m (MetaId, Term)
newValueMetaCtx frozen b cmp t tel perm ctx =
  mapSndM instantiateFull =<< newValueMetaCtx' frozen b cmp t tel perm ctx

{-# SPECIALIZE newValueMeta' :: RunMetaOccursCheck -> Comparison -> Type -> TCM (MetaId, Term) #-}
-- | Create a new value meta without η-expanding.
newValueMeta'
  :: MonadMetaSolver m
  => RunMetaOccursCheck -> Comparison -> Type -> m (MetaId, Term)
newValueMeta' b cmp t = do
  vs  <- getContextArgs
  tel <- getContextTelescope
  newValueMetaCtx' Instantiable b cmp t tel (idP $ size tel) vs

newValueMetaCtx'
  :: MonadMetaSolver m
  => Frozen -> RunMetaOccursCheck -> Comparison -> Type -> Telescope -> Permutation -> Args -> m (MetaId, Term)
newValueMetaCtx' frozen b cmp a tel perm vs = do
  i <- createMetaInfo' b
  let t     = telePi_ tel a
  x <- newMeta frozen i normalMetaPriority perm (HasType () cmp t)
  modality <- currentModality
  reportSDoc "tc.meta.new" 50 $ fsep
    [ text $ "new meta (" ++ show (i ^. lensIsAbstract) ++ "):"
    , nest 2 $ prettyTCM vs <+> "|-"
    , nest 2 $ pretty x <+> ":" <+> pretty modality <+> prettyTCM t
    ]
  etaExpandMetaSafe x
  -- Andreas, 2012-09-24: for Metas X : Size< u add constraint X+1 <= u
  let u = MetaV x $ map Apply vs
  boundedSizeMetaHook u tel a
  return (x, u)

newTelMeta :: MonadMetaSolver m => Telescope -> m Args
newTelMeta tel = newArgsMeta (abstract tel $ __DUMMY_TYPE__)

type Condition = Dom Type -> Abs Type -> Bool

trueCondition :: Condition
trueCondition _ _ = True

{-# SPECIALIZE newArgsMeta :: Type -> TCM Args #-}
newArgsMeta :: MonadMetaSolver m => Type -> m Args
newArgsMeta = newArgsMeta' trueCondition

{-# SPECIALIZE newArgsMeta' :: Condition -> Type -> TCM Args #-}
newArgsMeta' :: MonadMetaSolver m => Condition -> Type -> m Args
newArgsMeta' condition t = do
  args <- getContextArgs
  tel  <- getContextTelescope
  newArgsMetaCtx' Instantiable condition t tel (idP $ size tel) args

newArgsMetaCtx :: Type -> Telescope -> Permutation -> Args -> TCM Args
newArgsMetaCtx = newArgsMetaCtx' Instantiable trueCondition

newArgsMetaCtx''
  :: MonadMetaSolver m
  => MetaNameSuggestion -> Frozen -> Condition -> Type -> Telescope -> Permutation -> Args -> m Args
newArgsMetaCtx'' pref frozen condition (El s tm) tel perm ctx = do
  tm <- reduce tm
  case tm of
    Pi dom@(Dom{domInfo = info, unDom = a}) codom | condition dom codom -> do
      let mod  = getModality info
          -- Issue #3031: It's not enough to applyModalityToContext, since most (all?)
          -- of the context lives in tel. Don't forget the arguments in ctx.
          tel' = telFromList $
                 map (mod `inverseApplyModalityButNotQuantity`) $
                 telToList tel
          ctx' = map (mod `inverseApplyModalityButNotQuantity`) ctx
      (m, u) <- applyModalityToContext info $
                 newValueMetaCtx frozen RunMetaOccursCheck CmpLeq a tel' perm ctx'
      -- Jesper, 2021-05-05: When creating a metavariable from a
      -- generalizable variable, we must set the modality at which it
      -- will be generalized.  Don't do this for other metavariables,
      -- as they should keep the defaul modality (see #5363).
      whenM ((== YesGeneralizeVar) <$> viewTC eGeneralizeMetas) $
        setMetaGeneralizableArgInfo m $ hideOrKeepInstance info
      setMetaNameSuggestion m (suffixNameSuggestion pref (absName codom))
      args <- newArgsMetaCtx'' pref frozen condition (codom `absApp` u) tel perm ctx
      return $ Arg info u : args
    _  -> return []

newArgsMetaCtx'
  :: MonadMetaSolver m
  => Frozen -> Condition -> Type -> Telescope -> Permutation -> Args -> m Args
newArgsMetaCtx' = newArgsMetaCtx'' mempty

-- | Create a metavariable of record type. This is actually one metavariable
--   for each field.
newRecordMeta :: QName -> Args -> TCM Term
newRecordMeta r pars = do
  args <- getContextArgs
  tel  <- getContextTelescope
  newRecordMetaCtx mempty Instantiable r pars tel (idP $ size tel) args

newRecordMetaCtx
  :: MetaNameSuggestion
  -- ^ Name suggestion to be used as a /prefix/ of the name suggestions
  -- for the metas that represent each field
  -> Frozen  -- ^ Should the meta be created frozen?
  -> QName   -- ^ Name of record type
  -> Args    -- ^ Parameters of record type.
  -> Telescope -> Permutation -> Args -> TCM Term
newRecordMetaCtx pref frozen r pars tel perm ctx = do
  rdef   <- getRecordDef r
  let con = killRange $ _recConHead rdef
  -- Get the record field types as telescope.
  let ftel = apply (_recTel rdef) pars
  fields <- newArgsMetaCtx'' pref frozen trueCondition
              (telePi_ ftel __DUMMY_TYPE__) tel perm ctx
  return $ Con con ConOSystem (map Apply fields)

newQuestionMark :: InteractionId -> Comparison -> Type -> TCM (MetaId, Term)
newQuestionMark ii cmp = newQuestionMark' (newValueMeta' RunMetaOccursCheck) ii cmp


-- Since we are type-checking some code twice, e.g., record declarations
-- for the sake of the record constructor type and then again for the sake
-- of the record module (issue #434), we may encounter an interaction point
-- for which we already have a meta.  In this case, we want to reuse the meta.
-- Otherwise we get two meta for one interaction point which are not connected,
-- and e.g. Agda might solve one in some way
-- and the user the other in some other way...
--
-- New reference: Andreas, 2021-07-21, issues #5478 and #5463
-- Old reference: Andreas, 2016-07-29, issue 1720-2
-- See also: issue #2257
newQuestionMark'
  :: (Comparison -> Type -> TCM (MetaId, Term))
  -> InteractionId -> Comparison -> Type -> TCM (MetaId, Term)
newQuestionMark' new ii cmp t = lookupInteractionMeta ii >>= \case

  -- Case: new meta.
  Nothing -> do
    -- Do not run check for recursive occurrence of meta in definitions,
    -- because we want to give the recursive solution interactively (Issue 589)
    (x, m) <- new cmp t
    connectInteractionPoint ii x
    return (x, m)

  -- Case: existing meta.
  Just x -> do
    -- Get the context Γ in which the meta was created.
    MetaVar
      { mvInfo = MetaInfo{ miClosRange = Closure{ clEnv = TCEnv{ envContext = gamma }}}
      , mvPermutation = p
      } <- fromMaybe __IMPOSSIBLE__ <$> lookupLocalMeta' x
    -- Get the current context Δ.
    delta <- getContext
    -- A bit hazardous:
    -- we base our decisions on the names of the context entries.
    -- Ideally, Agda would organize contexts in ancestry trees
    -- with substitutions to move between parent and child.
    let glen = length gamma
    let dlen = length delta
    let gxs  = map (fst . unDom) gamma
    let dxs  = map (fst . unDom) delta
    reportSDoc "tc.interaction" 20 $ vcat
      [ "reusing meta"
      , nest 2 $ "creation context:" <+> pretty gxs
      , nest 2 $ "reusage  context:" <+> pretty dxs
      ]

    -- When checking a record declaration (e.g. Σ), creation context Γ
    -- might be of the forms Γ₀,Γ₁ or Γ₀,fst,Γ₁ or Γ₀,fst,snd,Γ₁ whereas
    -- Δ is of the form Γ₀,r,Γ₁,{Δ₂} for record variable r.
    -- So first find the record variable in Δ.
    rev_args <- case List.findIndex nameIsRecordName dxs of

      -- Case: no record variable in the context.
      -- Test whether Δ is an extension of Γ.
      Nothing -> do
        unless (gxs `List.isSuffixOf` dxs) $ do
          reportSDoc "impossible" 10 $ vcat
            [ "expecting meta-creation context"
            , nest 2 $ pretty gxs
            , "to be a suffix of the meta-reuse context"
            , nest 2 $ pretty dxs
            ]
          reportSDoc "impossible" 70 $ vcat
            [ "expecting meta-creation context"
            , nest 2 $ (text . show) gxs
            , "to be a suffix of the meta-reuse context"
            , nest 2 $ (text . show) dxs
            ]
          __IMPOSSIBLE__
        -- Apply the meta to |Γ| arguments from Δ.
        return $ map var [dlen - glen .. dlen - 1]

      -- Case: record variable in the context.
      Just k -> do
        -- Verify that the contexts relate as expected.
        let g0len = length dxs - k - 1
        -- Find out the Δ₂ and Γ₁ parts.
        -- However, as they do not share common ancestry, the @nameId@s differ,
        -- so we consider only the original concrete names.
        -- This is a bit risky... blame goes to #434.
        let gys = map nameCanonical gxs
        let dys = map nameCanonical dxs
        let (d2len, g1len) = findOverlap (take k dys) gys
        reportSDoc "tc.interaction" 30 $ vcat $ map (nest 2)
          [ "glen  =" <+> pretty glen
          , "g0len =" <+> pretty g0len
          , "g1len =" <+> pretty g1len
          , "d2len =" <+> pretty d2len
          ]
        -- The Γ₀ part should match.
        unless (drop (glen - g0len) gxs == drop (k + 1) dxs) $ do
          reportSDoc "impossible" 10 $ vcat
            [ "expecting meta-creation context (with fields instead of record var)"
            , nest 2 $ pretty gxs
            , "to share ancestry (suffix) with the meta-reuse context (with record var)"
            , nest 2 $ pretty dxs
            ]
          __IMPOSSIBLE__
        -- The Γ₁ part should match.
        unless ( ((==) `on` take g1len) gys (drop d2len dys) ) $ do
          reportSDoc "impossible" 10 $ vcat
            [ "expecting meta-creation context (with fields instead of record var)"
            , nest 2 $ pretty gxs
            , "to be an expansion of the meta-reuse context (with record var)"
            , nest 2 $ pretty dxs
            ]
          __IMPOSSIBLE__
        let (vs1, v : vs0) = splitAt g1len $ map var [d2len..dlen-1]
        -- We need to expand the record var @v@ into the correct number of fields.
        let numFields = glen - g1len - g0len
        if numFields <= 0 then return $ vs1 ++ vs0 else do
          -- Get the record type.
          let t = snd . unDom . fromMaybe __IMPOSSIBLE__ $ delta !!! k
          -- Get the record field names.
          fs <- getRecordTypeFields t
          -- Field arguments to the original meta are projections from the record var.
          let vfs = map ((\ x -> v `applyE` [Proj ProjSystem x]) . unDom) fs
          -- These are the final args to the original meta:
          return $ vs1 ++ reverse (take numFields vfs) ++ vs0

    -- Use ArgInfo from Γ.
    let args = reverse $ zipWith (<$) rev_args $ map argFromDom gamma
    -- Take the permutation into account (see TC.Monad.MetaVars.getMetaContextArgs).
    let vs = permute (takeP (length args) p) args
    reportSDoc "tc.interaction" 20 $ vcat
      [ "meta reuse arguments:" <+> prettyTCM vs ]
    return (x, MetaV x $ map Apply vs)

{-# SPECIALIZE blockTerm :: Type -> TCM Term -> TCM Term #-}
-- | Construct a blocked constant if there are constraints.
blockTerm
  :: (MonadMetaSolver m, MonadConstraint m, MonadFresh Nat m, MonadFresh ProblemId m)
  => Type -> m Term -> m Term
blockTerm t blocker = do
  (pid, v) <- newProblem blocker
  blockTermOnProblem t v pid

{-# SPECIALIZE blockTermOnProblem :: Type -> Term -> ProblemId -> TCM Term #-}
blockTermOnProblem
  :: (MonadMetaSolver m, MonadFresh Nat m)
  => Type -> Term -> ProblemId -> m Term
blockTermOnProblem t v pid = do
  -- Andreas, 2012-09-27 do not block on unsolved size constraints
  solved <- isProblemSolved pid
  ifM (return solved `or2M` isSizeProblem pid)
      (v <$ reportSLn "tc.meta.blocked" 20 ("Not blocking because " ++ show pid ++ " is " ++
                                            if solved then "solved" else "a size problem")) $ do
    i   <- createMetaInfo
    es  <- map Apply <$> getContextArgs
    tel <- getContextTelescope
    x   <- newMeta' (BlockedConst $ abstract tel v)
                    Instantiable
                    i
                    lowMetaPriority
                    (idP $ size tel)
                    (HasType () CmpLeq $ telePi_ tel t)
                    -- we don't instantiate blocked terms
    inTopContext $ addConstraint (unblockOnProblem pid) (UnBlock x)
    reportSDoc "tc.meta.blocked" 20 $ vcat
      [ "blocked" <+> prettyTCM x <+> ":=" <+> inTopContext
        (prettyTCM $ abstract tel v)
      , "     by" <+> (prettyTCM =<< getConstraintsForProblem pid)
      ]
    inst <- isInstantiatedMeta x
    if inst
      then instantiate (MetaV x es)
      else do
        -- We don't return the blocked term instead create a fresh metavariable
        -- that we compare against the blocked term once it's unblocked. This way
        -- blocked terms can be instantiated before they are unblocked, thus making
        -- constraint solving a bit more robust against instantiation order.
        -- Andreas, 2015-05-22: DontRunMetaOccursCheck to avoid Issue585-17.
        (m', v) <- newValueMeta DontRunMetaOccursCheck CmpLeq t
        reportSDoc "tc.meta.blocked" 30
          $   "setting twin of"
          <+> prettyTCM m'
          <+> "to be"
          <+> prettyTCM x
        updateMetaVar m' (\mv -> mv { mvTwin = Just x })
        i   <- fresh
        -- This constraint is woken up when unblocking, so it doesn't need a problem id.
        cmp <- buildProblemConstraint_ (unblockOnMeta x) (ValueCmp CmpEq (AsTermsOf t) v (MetaV x es))
        reportSDoc "tc.constr.add" 20 $ "adding constraint" <+> prettyTCM cmp
        listenToMeta (CheckConstraint i cmp) x
        return v

{-# SPECIALIZE blockTypeOnProblem :: Type -> ProblemId -> TCM Type #-}
blockTypeOnProblem
  :: (MonadMetaSolver m, MonadFresh Nat m)
  => Type -> ProblemId -> m Type
blockTypeOnProblem (El s a) pid = El s <$> blockTermOnProblem (sort s) a pid

-- | @unblockedTester t@ returns a 'Blocker' for @t@.
--
--   Auxiliary function used when creating a postponed type checking problem.
unblockedTester :: Type -> TCM Blocker
unblockedTester t = ifBlocked t (\ b _ -> return b) (\ _ _ -> return alwaysUnblock)

-- | Create a postponed type checking problem @e : t@ that waits for type @t@
--   to unblock (become instantiated or its constraints resolved).
postponeTypeCheckingProblem_ :: TypeCheckingProblem -> TCM Term
postponeTypeCheckingProblem_ p = do
  postponeTypeCheckingProblem p =<< unblock p
  where
    unblock (CheckExpr _ _ t)         = unblockedTester t
    unblock (CheckArgs _ _ _ _ t _ _) = unblockedTester t  -- The type of the head of the application.
    unblock (CheckProjAppToKnownPrincipalArg _ _ _ _ _ _ _ _ t _) = unblockedTester t -- The type of the principal argument
    unblock (CheckLambda _ _ _ t)     = unblockedTester t
    unblock (DoQuoteTerm _ _ _)       = __IMPOSSIBLE__     -- also quoteTerm problems

-- | Create a postponed type checking problem @e : t@ that waits for conditon
--   @unblock@.  A new meta is created in the current context that has as
--   instantiation the postponed type checking problem.  An 'UnBlock' constraint
--   is added for this meta, which links to this meta.
postponeTypeCheckingProblem :: TypeCheckingProblem -> Blocker -> TCM Term
postponeTypeCheckingProblem p unblock | unblock == alwaysUnblock = do
  reportSDoc "impossible" 2 $ "Postponed without blocker:" <?> prettyTCM p
  __IMPOSSIBLE__
postponeTypeCheckingProblem p unblock = do
  i   <- createMetaInfo' DontRunMetaOccursCheck
  tel <- getContextTelescope
  cl  <- buildClosure p
  let t = problemType p
  m   <- newMeta' (PostponedTypeCheckingProblem cl)
                  Instantiable i normalMetaPriority (idP (size tel))
         $ HasType () CmpLeq $ telePi_ tel t
  inTopContext $ reportSDoc "tc.meta.postponed" 20 $ vcat
    [ "new meta" <+> prettyTCM m <+> ":" <+> prettyTCM (telePi_ tel t)
    , "for postponed typechecking problem" <+> prettyTCM p
    ]

  -- Create the meta that we actually return
  -- Andreas, 2012-03-15
  -- This is an alias to the pptc meta, in order to allow pruning (issue 468)
  -- and instantiation.
  -- Since this meta's solution comes from user code, we do not need
  -- to run the extended occurs check (metaOccurs) to exclude
  -- non-terminating solutions.
  es  <- map Apply <$> getContextArgs
  (_, v) <- newValueMeta DontRunMetaOccursCheck CmpLeq t
  cmp <- buildProblemConstraint_ (unblockOnMeta m) (ValueCmp CmpEq (AsTermsOf t) v (MetaV m es))
  reportSDoc "tc.constr.add" 20 $ "adding constraint" <+> prettyTCM cmp
  i   <- liftTCM fresh
  listenToMeta (CheckConstraint i cmp) m
  addConstraint unblock (UnBlock m)
  return v

-- | Type of the term that is produced by solving the 'TypeCheckingProblem'.
problemType :: TypeCheckingProblem -> Type
problemType (CheckExpr _ _ t         ) = t
problemType (CheckArgs _ _ _ _ _ t _ ) = t  -- The target type of the application.
problemType (CheckProjAppToKnownPrincipalArg _ _ _ _ _ t _ _ _ _) = t -- The target type of the application
problemType (CheckLambda _ _ _ t     ) = t
problemType (DoQuoteTerm _ _ t)        = t

-- | Eta-expand a local meta-variable, if it is of the specified kind.
--   Don't do anything if the meta-variable is a blocked term.
etaExpandMetaTCM :: [MetaClass] -> MetaId -> TCM ()
etaExpandMetaTCM kinds m = whenM ((not <$> isFrozen m) `and2M` asksTC envAssignMetas `and2M` isEtaExpandable kinds m) $ do
  verboseBracket "tc.meta.eta" 20 ("etaExpandMeta " ++ prettyShow m) $ do
    let waitFor b = do
          reportSDoc "tc.meta.eta" 20 $ do
            "postponing eta-expansion of meta variable" <+>
              prettyTCM m <+>
              "which is blocked by" <+> prettyTCM b
          mapM_ (listenToMeta (EtaExpand m)) $ allBlockingMetas b
        dontExpand = do
          reportSDoc "tc.meta.eta" 20 $ do
            "we do not expand meta variable" <+> prettyTCM m <+>
              text ("(requested was expansion of " ++ show kinds ++ ")")
    meta <- lookupLocalMeta m
    case mvJudgement meta of
      IsSort{} -> dontExpand
      HasType _ cmp a -> do

        reportSDoc "tc.meta.eta" 40 $ sep
          [ text "considering eta-expansion at type "
          , prettyTCM a
          , text " raw: "
          , pretty a
          ]

        TelV tel b <- telView a
        reportSDoc "tc.meta.eta" 40 $ sep
          [ text "considering eta-expansion at type"
          , addContext tel (prettyTCM b)
          , text "under telescope"
          , prettyTCM tel
          ]

        -- Eta expanding metas with a domFinite will just make sure
        -- they go unsolved: conversion will compare them at the
        -- different cases for the domain, so it will not find the
        -- solution for the whole meta.
        if any domIsFinite (flattenTel tel) then dontExpand else do

        -- Issue #3774: continue with the right context for b
        addContext tel $ do

        -- if the target type @b@ of @m@ is a meta variable @x@ itself
        -- (@NonBlocked (MetaV{})@),
        -- or it is blocked by a meta-variable @x@ (@Blocked@), we cannot
        -- eta expand now, we have to postpone this.  Once @x@ is
        -- instantiated, we can continue eta-expanding m.  This is realized
        -- by adding @m@ to the listeners of @x@.
        ifBlocked (unEl b) (\ x _ -> waitFor x) $ \ _ t -> case t of
          lvl@(Def r es) ->
            ifM (isEtaRecord r) {- then -} (do
              let ps = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
              let expand = do
                    u <- withMetaInfo' meta $
                      newRecordMetaCtx (miNameSuggestion (mvInfo meta))
                        (mvFrozen meta) r ps tel (idP $ size tel) $ teleArgs tel
                    -- Andreas, 2019-03-18, AIM XXIX, issue #3597
                    -- When meta is frozen instantiate it with in-turn frozen metas.
                    inTopContext $ do
                      reportSDoc "tc.meta.eta" 15 $ sep
                          [ "eta expanding: " <+> pretty m <+> " --> "
                          , nest 2 $ prettyTCM u
                          ]
                      -- Andreas, 2012-03-29: No need for occurrence check etc.
                      -- we directly assign the solution for the meta
                      -- 2012-05-23: We also bypass the check for frozen.
                      noConstraints $ assignTerm' m (telToArgs tel) u  -- should never produce any constraints
              if Records `elem` kinds then
                expand
               else if (SingletonRecords `elem` kinds) then
                catchPatternErr (\x -> waitFor x) $ do
                 ifM (isSingletonRecord r ps) expand dontExpand
                else dontExpand
            ) $ {- else -} ifM (andM [ return $ Levels `elem` kinds
                            , typeInType
                            , (Just lvl ==) <$> getBuiltin' builtinLevel
                            ]) (do
              reportSLn "tc.meta.eta" 20 $ "Expanding level meta to 0 (type-in-type)"
              -- Andreas, 2012-03-30: No need for occurrence check etc.
              -- we directly assign the solution for the meta
              noConstraints $ assignTerm m (telToArgs tel) $ Level $ ClosedLevel 0
           ) $ {- else -} dontExpand
          _ -> dontExpand

-- | Eta expand blocking metavariables of record type, and reduce the
-- blocked thing.

etaExpandBlocked :: (MonadReduce m, MonadMetaSolver m, IsMeta t, Reduce t)
                 => Blocked t -> m (Blocked t)
etaExpandBlocked t@NotBlocked{} = return t
etaExpandBlocked t@(Blocked _ v) | Just{} <- isMeta v = return t
etaExpandBlocked (Blocked b t)  = do
  reportSDoc "tc.meta.eta" 30 $ "Eta expanding blockers" <+> pretty b
  mapM_ (etaExpandMeta [Records]) $ allBlockingMetas b
  t <- reduceB t
  case t of
    Blocked b' _ | b /= b' -> etaExpandBlocked t
    _                      -> return t

{-# SPECIALIZE assignWrapper :: CompareDirection -> MetaId -> Elims -> Term -> TCM () -> TCM () #-}
assignWrapper :: (MonadMetaSolver m, MonadConstraint m, MonadError TCErr m, MonadDebug m, HasOptions m)
              => CompareDirection -> MetaId -> Elims -> Term -> m () -> m ()
assignWrapper dir x es v doAssign = do
  ifNotM (asksTC envAssignMetas) dontAssign $ {- else -} do
    reportSDoc "tc.meta.assign" 10 $ do
      "term" <+> prettyTCM (MetaV x es) <+> text (":" ++ prettyShow dir) <+> prettyTCM v
    nowSolvingConstraints doAssign `finally` solveAwakeConstraints

  where dontAssign = do
          reportSLn "tc.meta.assign" 10 "don't assign metas"
          patternViolation alwaysUnblock  -- retry again when we are allowed to instantiate metas

-- | Miller pattern unification:
--
--   @assign dir x vs v a@ solves problem @x vs <=(dir) v : a@ for meta @x@
--   if @vs@ are distinct variables (linearity check)
--   and @v@ depends only on these variables
--   and does not contain @x@ itself (occurs check).
--
--   This is the basic story, but we have added some features:
--
--   1. Pruning.
--   2. Benign cases of non-linearity.
--   3. @vs@ may contain record patterns.
--
--   For a reference to some of these extensions, read
--   Andreas Abel and Brigitte Pientka's TLCA 2011 paper.

assign :: CompareDirection -> MetaId -> Args -> Term -> CompareAs -> TCM ()
assign dir x args v target = addOrUnblocker (unblockOnMeta x) $ do

  mvar <- lookupLocalMeta x  -- information associated with meta x
  let t = jMetaType $ mvJudgement mvar

  -- Andreas, 2011-05-20 TODO!
  -- full normalization  (which also happens during occurs check)
  -- is too expensive! (see Issue 415)
  -- need to do something cheaper, especially if
  -- we are dealing with a Miller pattern that can be solved
  -- immediately!
  -- Ulf, 2011-08-25 DONE!
  -- Just instantiating the top-level meta, which is cheaper. The occurs
  -- check will first try without unfolding any definitions (treating
  -- arguments to definitions as flexible), if that fails it tries again
  -- with full unfolding.
  reportSDoc "tc.meta.assign" 25 $ "v = " <+> prettyTCM v
  v <- instantiate v
  reportSDoc "tc.meta.assign" 25 $ "v = " <+> prettyTCM v
  reportSDoc "tc.meta.assign" 45 $
    "MetaVars.assign: assigning meta " <+> prettyTCM (MetaV x []) <+>
    " with args " <+> prettyList_ (map (prettyTCM . unArg) args) <+>
    " to " <+> prettyTCM v
  reportSDoc "tc.meta.assign" 45 $
    "MetaVars.assign: type of meta: " <+> prettyTCM t

  reportSDoc "tc.meta.assign" 75 $
    text "MetaVars.assign: assigning meta  " <> pretty x <> text "  with args  " <> pretty args <> text "  to  " <> pretty v

  let
    boundary v = do
      cubical <- cubicalOption
      isip <- isInteractionMetaB x args
      case (,) <$> cubical <*> isip of
        Just (_, (x, ip, args)) -> tryAddBoundary dir x ip args v target
        _ -> pure ()

  case (v, mvJudgement mvar) of
      (Sort s, HasType{}) -> hasBiggerSort s
      _                   -> return ()

  -- Jesper, 2019-09-13: When --no-sort-comparison is enabled,
  -- we equate the sort of the solution with the sort of the
  -- metavariable, in order to solve metavariables in sorts.
  -- Jesper, 2020-04-22: We do this before any of the other steps
  -- because comparing the sorts might lead to some metavariables
  -- being solved, which can help with pruning (see #4615).
  -- Jesper, 2020-08-25: --no-sort-comparison is now the default
  -- behaviour.
  --
  -- Under most circumstances, the conversion checker guarantees that
  -- the solution for the meta has the correct type, so there is no
  -- need to check anything. However, there are two circumstances in
  -- which we do need to check the type of the solution:
  --
  -- 1. When comparing two types they are not guaranteed to have the
  --    same sort.
  --
  -- 2. When --cumulativity is enabled the same can happen when
  --    comparing two terms at a sort type.

  cumulativity <- optCumulativity <$> pragmaOptions

  let checkSolutionSort cmp s v = do
        s' <- sortOf v
        reportSDoc "tc.meta.assign" 40 $
          "Instantiating sort" <+> prettyTCM s <+>
          "to sort" <+> prettyTCM s' <+> "of solution" <+> prettyTCM v
        traceCall (CheckMetaSolution (getRange mvar) x (sort s) v) $
          compareSort cmp s' s

  case (target , mvJudgement mvar) of
    -- Case 1 (comparing term to meta as types)
    (AsTypes{}   , HasType _ cmp0 t) -> do
        let cmp   = if cumulativity then cmp0 else CmpEq
            abort = patternViolation =<< updateBlocker (unblockOnAnyMetaIn t) -- TODO: make piApplyM' compute unblocker
        t' <- piApplyM' abort t args
        s <- shouldBeSort t'
        checkSolutionSort cmp s v

    -- Case 2 (comparing term to type-level meta as terms, with --cumulativity)
    (AsTermsOf{} , HasType _ cmp t)
      | cumulativity -> do
          let abort = patternViolation =<< updateBlocker (unblockOnAnyMetaIn t)
          t' <- piApplyM' abort t args
          TelV tel t'' <- telView t'
          addContext tel $ ifNotSort t'' (return ()) $ \s -> do
            let v' = raise (size tel) v `apply` teleArgs tel
            checkSolutionSort cmp s v'

    (AsTypes{}   , IsSort{}       ) -> return ()
    (AsTermsOf{} , _              ) -> return ()
    (AsSizes{}   , _              ) -> return ()  -- TODO: should we do something similar for sizes?



  -- We don't instantiate frozen mvars
  when (mvFrozen mvar == Frozen) $ do
    reportSLn "tc.meta.assign" 25 $ "aborting: meta is frozen!"
    -- IApplyConfluence can contribute boundary conditions to frozen metas
    boundary v
    patternViolation neverUnblock

  -- We never get blocked terms here anymore. TODO: we actually do. why?
  whenM (isBlockedTerm x) $ do
    reportSLn "tc.meta.assign" 25 $ "aborting: meta is a blocked term!"
    patternViolation (unblockOnMeta x)

  -- Andreas, 2010-10-15 I want to see whether rhs is blocked
  reportSLn "tc.meta.assign" 50 $ "MetaVars.assign: I want to see whether rhs is blocked"
  reportSDoc "tc.meta.assign" 25 $ do
    v0 <- reduceB v
    case v0 of
      Blocked m0 _ -> "r.h.s. blocked on:" <+> prettyTCM m0
      NotBlocked{} -> "r.h.s. not blocked"
  reportSDoc "tc.meta.assign" 25 $ "v = " <+> prettyTCM v

  -- Turn the assignment problem @_X args >= SizeLt u@ into
  -- @_X args = SizeLt (_Y args@ and constraint
  -- @_Y args >= u@.
  subtypingForSizeLt dir x mvar t args v $ \ v -> do

    reportSDoc "tc.meta.assign" 25 $ "v = " <+> prettyTCM v
    reportSDoc "tc.meta.assign.proj" 45 $ do
      cxt <- getContextTelescope
      vcat
        [ "context before projection expansion"
        , nest 2 $ inTopContext $ prettyTCM cxt
        ]

    -- Normalise and eta contract the arguments to the meta. These are
    -- usually small, and simplifying might let us instantiate more metas.
    -- Also, try to expand away projected vars in meta args.

    expandProjectedVars args (v, target) $ \ args (v, target) -> do

      reportSDoc "tc.meta.assign.proj" 45 $ do
        cxt <- getContextTelescope
        vcat
          [ "context after projection expansion"
          , nest 2 $ inTopContext $ prettyTCM cxt
          ]

      -- Andreas, 2019-11-16, issue #4159:
      -- We would like to save the work we put into expanding projected variables.
      -- However, the Conversion checker speculatively tries some assignment
      -- in some places (e.g. shortcut) and relies on an exception to be thrown
      -- to try other alternatives next.
      -- If we catch the exception here, this (brittle) mechanism will be broken.
      -- Maybe one possibility would be to rethrow the exception with the
      -- new constraint.  Then, further up, it could be decided whether
      -- to discard the new constraint and do something different,
      -- or add the new constraint when postponing.

      -- BEGIN attempt #4159
      -- let constraint = case v of
      --       -- Sort s -> dirToCmp SortCmp dir (MetaS x $ map Apply args) s
      --       _      -> dirToCmp (\ cmp -> ValueCmp cmp target) dir (MetaV x $ map Apply args) v
      -- reportSDoc "tc.meta.assign.catch" 40 $ sep
      --   [ "assign: catching constraint:"
      --   , prettyTCM constraint
      --   ]
      -- -- reportSDoc "tc.meta.assign.catch" 60 $ sep
      -- --   [ "assign: catching constraint:"
      -- --   , pretty constraint
      -- --   ]
      -- reportSDoc "tc.meta.assign.catch" 80 $ sep
      --   [ "assign: catching constraint (raw):"
      --   , (text . show) constraint
      --   ]
      -- catchConstraint constraint $ do
      -- END attempt #4159


      -- Andreas, 2011-04-21 do the occurs check first
      -- e.g. _1 x (suc x) = suc (_2 x y)
      -- even though the lhs is not a pattern, we can prune the y from _2

      let
                vars              = freeVars args
                relevantVL        = filterVarMapToList isRelevant vars
                shapeIrrelevantVL = filterVarMapToList isShapeIrrelevant vars
                irrelevantVL      = filterVarMapToList (liftM2 (&&) isIrrelevant isUnguarded) vars
            -- Andreas, 2011-10-06 only irrelevant vars that are direct
            -- arguments to the meta, hence, can be abstracted over, may
            -- appear on the rhs.  (test/fail/Issue483b)
            -- Update 2011-03-27: Also irr. vars under record constructors.
            -- Andreas, 2019-06-25:  The reason is that when solving
            -- @X args = v@ we drop all irrelevant arguments that
            -- are not variables (after flattening of record constructors).
            -- (See isVarOrIrrelevant in inverseSubst.)
            -- Thus, the occurs-check needs to ensure only these variables
            -- are mentioned on the rhs.
            -- In the terminology of free variable analysis, the retained
            -- irrelevant variables are exactly the Unguarded ones.
            -- Jesper, 2019-10-15: This is actually wrong since it
            -- will lead to pruning of metas that should not be
            -- pruned, see #4136.

      reportSDoc "tc.meta.assign" 20 $
          let pr (Var n []) = text (show n)
              pr (Def c []) = prettyTCM c
              pr _          = ".."
          in vcat
               [ "mvar args:" <+> sep (map (pr . unArg) args)
               , "fvars lhs (relevant)        :" <+> sep (map (text . show) relevantVL)
               , "fvars lhs (shape-irrelevant):" <+> sep (map (text . show) shapeIrrelevantVL)
               , "fvars lhs (irrelevant)      :" <+> sep (map (text . show) irrelevantVL)
               ]

      -- Check that the x doesn't occur in the right hand side.
      -- Prune mvars on rhs such that they can only depend on lhs vars.
      -- Herein, distinguish relevant and irrelevant vars,
      -- since when abstracting irrelevant lhs vars, they may only occur
      -- irrelevantly on rhs.
      -- v <- liftTCM $ occursCheck x (relevantVL, nonstrictVL, irrelevantVL) v
      v <- liftTCM $ occursCheck x vars v

      reportSLn "tc.meta.assign" 15 "passed occursCheck"
      reportSDoc "tc.meta.assign" 25 $ "v = " <+> prettyTCM v
      verboseS "tc.meta.assign" 30 $ do
        let n = termSize v
        when (n > 200) $ reportSDoc "tc.meta.assign" 30 $
          sep [ "size" <+> text (show n)
--              , nest 2 $ "type" <+> prettyTCM t
              , nest 2 $ "term" <+> prettyTCM v
              ]

      -- Check linearity of @ids@
      -- Andreas, 2010-09-24: Herein, ignore the variables which are not
      -- free in v
      -- Ulf, 2011-09-22: we need to respect irrelevant vars as well, otherwise
      -- we'll build solutions where the irrelevant terms are not valid
      let fvs = allFreeVars v
      reportSDoc "tc.meta.assign" 20 $
        "fvars rhs:" <+> sep (map (text . show) $ VarSet.toList fvs)

      -- Check that the arguments are variables
      mids <- do
        res <- runExceptT $ inverseSubst' (const False) args
        case res of
          -- all args are variables
          Right ids -> do
            reportSDoc "tc.meta.assign" 60 $
              "inverseSubst returns:" <+> sep (map pretty ids)
            reportSDoc "tc.meta.assign" 50 $
              "inverseSubst returns:" <+> sep (map prettyTCM ids)
            let boundVars = VarSet.fromList $ map fst ids
            if fvs `VarSet.isSubsetOf` boundVars
              then return $ Just ids
              else return Nothing
          -- we have proper values as arguments which could be cased on
          -- here, we cannot prune, since offending vars could be eliminated
          Left (CantInvert tm) -> Nothing <$ boundary v
          -- we have non-variables, but these are not eliminateable
          Left NeutralArg  -> Just <$> attemptPruning x args fvs
          -- we have a projected variable which could not be eta-expanded away:
          -- same as neutral
          Left ProjVar{}   -> Just <$> attemptPruning x args fvs

      case mids of  -- vv Ulf 2014-07-13: actually not needed after all: attemptInertRHSImprovement x args v
        Nothing  -> patternViolation =<< updateBlocker (unblockOnAnyMetaIn v)  -- TODO: more precise
        Just ids -> do
          -- Check linearity
          ids <- do
            res <- runExceptT $ checkLinearity {- (`VarSet.member` fvs) -} ids
            case res of
              -- case: linear
              Right ids -> return ids
              -- case: non-linear variables that could possibly be pruned
              -- If pruning fails we need to unblock on any meta in the rhs, since they might get
              -- rid of the dependency on the non-linear variable. TODO: be more precise (all metas
              -- using non-linear variables need to be solved).
              Left ()   -> do
                block <- updateBlocker $ unblockOnAnyMetaIn v
                addOrUnblocker block $ attemptPruning x args fvs

          -- Check ids is time respecting.
          () <- do
            let idvars = map (mapSnd allFreeVars) ids
            -- earlierThan α v := v "arrives" before α
            let earlierThan l j = j > l
            TelV tel' _ <- telViewUpToPath (length args) t
            forM_ ids $ \(i,u) -> do
              d <- lookupBV i
              case getLock (getArgInfo d) of
                IsNotLock -> pure ()
                IsLock{} -> do
                let us = IntSet.unions $ map snd $ filter (earlierThan i . fst) idvars
                -- us Earlier than u
                unlessM (addContext tel' $ checkEarlierThan u us) $
                  patternViolation (unblockOnMeta x)  -- If the earlier check hard-fails we need to
                                                      -- solve this meta in some other way.

          let n = length args
          TelV tel' _ <- telViewUpToPath n t

          -- Check subtyping constraints on the context variables.

          -- Intuition: suppose @_X : (x : A) → B@, then to turn
          --   @
          --     Γ(x : A') ⊢ _X x =?= v : B'@
          --   @
          -- into
          --   @
          --     Γ ⊢ _X =?= λ x → v
          --   @
          -- we need to check that @A <: A'@ (due to contravariance).
          let sigma = parallelS $ reverse $ map unArg args
          hasSubtyping <- optCumulativity <$> pragmaOptions
          when hasSubtyping $ forM_ ids $ \(i , u) -> do
            -- @u@ is a (projected) variable, so we can infer its type
            a  <- applySubst sigma <$> addContext tel' (infer u)
            a' <- typeOfBV i
            checkSubtypeIsEqual a' a
              `catchError` \case
                TypeError{} -> patternViolation (unblockOnMeta x) -- If the subtype check hard-fails we need to
                err         -> throwError err                     -- solve this meta in some other way.

          -- Solve.
          m <- getContextSize
          assignMeta' m x t n ids v
  where
    -- Try to remove meta arguments from lhs that mention variables not occurring on rhs.
    attemptPruning
      :: MetaId  -- Meta-variable (lhs)
      -> Args    -- Meta arguments (lhs)
      -> FVs     -- Variables occuring on the rhs
      -> TCM a
    attemptPruning x args fvs = do
      -- non-linear lhs: we cannot solve, but prune
      killResult <- prune x args $ (`VarSet.member` fvs)
      let success = killResult `elem` [PrunedSomething,PrunedEverything]
      reportSDoc "tc.meta.assign" 10 $
        "pruning" <+> prettyTCM x <+> do text $ if success then "succeeded" else "failed"
      blocker <- if
        | success   -> return alwaysUnblock  -- If pruning succeeded we want to retry right away
        | otherwise -> unblockOnAnyMetaIn . MetaV x . map Apply <$> instantiateFull args
             -- TODO: could be more precise: only unblock on metas
             --       applied to offending variables
      patternViolation blocker

-- | Is the given metavariable application secretly an interaction point
-- application? Ugly.
isInteractionMetaB
  :: forall m. (ReadTCState m, MonadReduce m, MonadPretty m)
  => MetaId
  -> Args
  -> m (Maybe (MetaId, InteractionId, Args))
isInteractionMetaB mid args =
  runMaybeT $ here mid args `mplus` do
    -- If the meta isn't literally an interaction point it might still
    -- be instantiable to an interaction point, as long as we ignore
    -- blocking
    lift (instantiateBlockingFull (MetaV mid (Apply <$> args))) >>= there
  where
    here mid args = do
      iid <- MaybeT (isInteractionMeta mid)
      pure (mid, iid, args)

    instantiateBlockingFull = locallyTCState stInstantiateBlocking (const True) . instantiateFull

    there :: Term -> MaybeT m (MetaId, InteractionId, Args)
    there (MetaV m args) = do
      iid  <- MaybeT (isInteractionMeta m)
      args <- MaybeT (pure (allApplyElims args))
      pure (m, iid, args)
    -- It might be the case that the inner meta (the interaction point)
    -- exists in a larger context, so instantiating the outer meta (the
    -- original argument) will produce lambdas.
    --
    -- Since the boundary code runs in the inner, larger context, we can
    -- peel off the lambdas without running afoul of the scope.
    there (Lam _ as) = there (absApp as (var 0))
    there _ = mzero

{- UNUSED
-- | When faced with @_X us == D vs@ for an inert D we can solve this by
--   @_X xs := D _Ys@ with new constraints @_Yi us == vi@. This is important
--   for instance arguments, where knowing the head D might enable progress.
attemptInertRHSImprovement :: MetaId -> Args -> Term -> TCM ()
attemptInertRHSImprovement m args v = do
  reportSDoc "tc.meta.inert" 30 $ vcat
    [ "attempting inert rhs improvement"
    , nest 2 $ sep [ prettyTCM (MetaV m $ map Apply args) <+> "=="
                   , prettyTCM v ] ]
  -- Check that the right-hand side has the form D vs, for some inert constant D.
  -- Returns the type of D and a function to build an application of D.
  (a, mkRHS) <- ensureInert v
  -- Check that all arguments to the meta are neutral and does not have head D.
  -- If there are non-neutral arguments there could be solutions to the meta
  -- that computes over these arguments. If D is an argument to the meta we get
  -- multiple solutions (for instance: _M Nat == Nat can be solved by both
  -- _M := \ x -> x and _M := \ x -> Nat).
  mapM_ (ensureNeutral (mkRHS []) . unArg) args
  tel <- theTel <$> (telView =<< getMetaType m)
  -- When attempting shortcut meta solutions, metas aren't necessarily fully
  -- eta expanded. If this is the case we skip inert improvement.
  when (length args < size tel) $ do
    reportSDoc "tc.meta.inert" 30 $ "not fully applied"
    patternViolation
  -- Solve the meta with _M := \ xs -> D (_Y1 xs) .. (_Yn xs), for fresh metas
  -- _Yi.
  metaArgs <- inTopContext $ addContext tel $ newArgsMeta a
  let varArgs = map Apply $ reverse $ zipWith (\i a -> var i <$ a) [0..] (reverse args)
      sol     = mkRHS metaArgs
      argTel  = map ("x" <$) args
  reportSDoc "tc.meta.inert" 30 $ nest 2 $ vcat
    [ "a       =" <+> prettyTCM a
    , "tel     =" <+> prettyTCM tel
    , "metas   =" <+> prettyList (map prettyTCM metaArgs)
    , "sol     =" <+> prettyTCM sol
    ]
  assignTerm m argTel sol
  patternViolation  -- throwing a pattern violation here lets the constraint
                    -- machinery worry about restarting the comparison.
  where
    ensureInert :: Term -> TCM (Type, Args -> Term)
    ensureInert v = do
      let notInert = do
            reportSDoc "tc.meta.inert" 30 $ nest 2 $ "not inert:" <+> prettyTCM v
            patternViolation
          toArgs elims =
            case allApplyElims elims of
              Nothing -> do
                reportSDoc "tc.meta.inert" 30 $ nest 2 $ "can't do projections from inert"
                patternViolation
              Just args -> return args
      case v of
        Var x elims -> (, Var x . map Apply) <$> typeOfBV x
        Con c ci args  -> notInert -- (, Con c ci) <$> defType <$> getConstInfo (conName c)
        Def f elims -> do
          def <- getConstInfo f
          let good = return (defType def, Def f . map Apply)
          case theDef def of
            Axiom{}       -> good
            Datatype{}    -> good
            Record{}      -> good
            Function{}    -> notInert
            Primitive{}   -> notInert
            Constructor{} -> __IMPOSSIBLE__

        Pi{}       -> notInert -- this is actually inert but improving doesn't buy us anything for Pi
        Lam{}      -> notInert
        Sort{}     -> notInert
        Lit{}      -> notInert
        Level{}    -> notInert
        MetaV{}    -> notInert
        DontCare{} -> notInert

    ensureNeutral :: Term -> Term -> TCM ()
    ensureNeutral rhs v = do
      b <- reduceB v
      let notNeutral v = do
            reportSDoc "tc.meta.inert" 30 $ nest 2 $ "not neutral:" <+> prettyTCM v
            patternViolation
          checkRHS arg
            | arg == rhs = do
              reportSDoc "tc.meta.inert" 30 $ nest 2 $ "argument shares head with RHS:" <+> prettyTCM arg
              patternViolation
            | otherwise  = return ()
      case b of
        Blocked{}      -> notNeutral v
        NotBlocked r v ->                      -- Andrea(s) 2014-12-06 can r be useful?
          case v of
            Var x _    -> checkRHS (Var x [])
            Def f _    -> checkRHS (Def f [])
            Pi{}       -> return ()
            Sort{}     -> return ()
            Level{}    -> return ()
            Lit{}      -> notNeutral v
            DontCare{} -> notNeutral v
            Con{}      -> notNeutral v
            Lam{}      -> notNeutral v
            MetaV{}    -> __IMPOSSIBLE__
-- END UNUSED -}

-- | @assignMeta m x t ids u@ solves @x ids = u@ for meta @x@ of type @t@,
--   where term @u@ lives in a context of length @m@.
--   Precondition: @ids@ is linear.
assignMeta :: Int -> MetaId -> Type -> [Int] -> Term -> TCM ()
assignMeta m x t ids v = do
  let n    = length ids
      cand = List.sort $ zip ids $ map var $ downFrom n
  assignMeta' m x t n cand v

-- | @assignMeta' m x t ids u@ solves @x = [ids]u@ for meta @x@ of type @t@,
--   where term @u@ lives in a context of length @m@,
--   and @ids@ is a partial substitution.
assignMeta' :: Int -> MetaId -> Type -> Int -> SubstCand -> Term -> TCM ()
assignMeta' m x t n ids v = do
  -- we are linear, so we can solve!
  reportSDoc "tc.meta.assign" 25 $
      "preparing to instantiate: " <+> prettyTCM v

  -- Rename the variables in v to make it suitable for abstraction over ids.
  -- Basically, if
  --   Γ   = a b c d e
  --   ids = d b e
  -- then
  --   v' = (λ a b c d e. v) _ 1 _ 2 0
  --
  -- Andreas, 2013-10-25 Solve using substitutions:
  -- Convert assocList @ids@ (which is sorted) into substitution,
  -- filling in __IMPOSSIBLE__ for the missing terms, e.g.
  -- [(0,0),(1,2),(3,1)] --> [0, 2, __IMP__, 1, __IMP__]
  -- ALT 1: O(m * size ids), serves as specification
  -- let ivs = [fromMaybe __IMPOSSIBLE__ $ lookup i ids | i <- [0..m-1]]
  -- ALT 2: O(m)
  let assocToList i = \case
        _           | i >= m -> []
        ((j,u) : l) | i == j -> Just u  : assocToList (i + 1) l
        l                    -> Nothing : assocToList (i + 1) l
      ivs = assocToList 0 ids
      rho = prependS impossible ivs $ raiseS n
      v'  = applySubst rho v

  -- Metas are top-level so we do the assignment at top-level.
  inTopContext $ do
    -- Andreas, 2011-04-18 to work with irrelevant parameters
    -- we need to construct tel' from the type of the meta variable
    -- (no longer from ids which may not be the complete variable list
    -- any more)
    reportSDoc "tc.meta.assign" 15 $ "type of meta =" <+> prettyTCM t

    (telv@(TelV tel' a), bs) <- telViewUpToPathBoundary n t
    reportSDoc "tc.meta.assign" 30 $ "tel'  =" <+> prettyTCM tel'
    reportSDoc "tc.meta.assign" 30 $ "#args =" <+> text (show n)
    -- Andreas, 2013-09-17 (AIM XVIII): if t does not provide enough
    -- types for the arguments, it might be blocked by a meta;
    -- then we give up. (Issue 903)
    when (size tel' < n) $ do
      a <- abortIfBlocked a
      reportSDoc "impossible" 10 $ "not enough pis, but not blocked?" <?> pretty a
      __IMPOSSIBLE__   -- If we get here it was _not_ blocked by a meta!

    -- Perform the assignment (and wake constraints).

    let vsol = abstract tel' v'

    -- Andreas, 2013-10-25 double check solution before assigning
    whenM (optDoubleCheck  <$> pragmaOptions) $ do
      m <- lookupLocalMeta x
      reportSDoc "tc.meta.check" 30 $ "double checking solution"
      catchConstraint (CheckMetaInst x) $
        addContext tel' $ checkSolutionForMeta x m v' a

    reportSDoc "tc.meta.assign" 10 $
      "solving" <+> prettyTCM x <+> ":=" <+> prettyTCM vsol

    v' <- blockOnBoundary telv bs v'

    assignTerm x (telToArgs tel') v'
  where
    blockOnBoundary :: TelView -> Boundary -> Term -> TCM Term
    blockOnBoundary telv         [] v = return v
    blockOnBoundary (TelV tel t) bs v = addContext tel $
      blockTerm t $ do
        neg <- primINeg
        forM_ bs $ \ (r,(x,y)) -> do
          equalTermOnFace (neg `apply1` r) t x v
          equalTermOnFace r  t y v
        return v

-- | Check that the instantiation of the given metavariable fits the
--   type of the metavariable. If the metavariable is not yet
--   instantiated, add a constraint to check the instantiation later.
checkMetaInst :: MetaId -> TCM ()
checkMetaInst x = do
  m <- lookupLocalMeta x
  let postpone = addConstraint (unblockOnMeta x) $ CheckMetaInst x
  case mvInstantiation m of
    BlockedConst{} -> postpone
    PostponedTypeCheckingProblem{} -> postpone
    OpenMeta{} -> postpone
    InstV inst -> do
      let n = size (instTel inst)
          t = jMetaType $ mvJudgement m
      (telv@(TelV tel a),bs) <- telViewUpToPathBoundary n t
      catchConstraint (CheckMetaInst x) $ addContext tel $
        checkSolutionForMeta x m (instBody inst) a

-- | Check that the instantiation of the metavariable with the given
--   term is well-typed.
checkSolutionForMeta :: MetaId -> MetaVariable -> Term -> Type -> TCM ()
checkSolutionForMeta x m v a = do
  reportSDoc "tc.meta.check" 30 $ "checking solution for meta" <+> prettyTCM x
  case mvJudgement m of
    HasType{ jComparison = cmp } -> do
      reportSDoc "tc.meta.check" 30 $ nest 2 $
        prettyTCM x <+> " : " <+> prettyTCM a <+> ":=" <+> prettyTCM v
      reportSDoc "tc.meta.check" 50 $ nest 2 $ do
        ctx <- getContext
        inTopContext $ "in context: " <+> prettyTCM (PrettyContext ctx)
      traceCall (CheckMetaSolution (getRange m) x a v) $
        checkInternal v cmp a
    IsSort{}  -> void $ do
      reportSDoc "tc.meta.check" 30 $ nest 2 $
        prettyTCM x <+> ":=" <+> prettyTCM v <+> " is a sort"
      s <- shouldBeSort (El __DUMMY_SORT__ v)
      traceCall (CheckMetaSolution (getRange m) x (sort (univSort s)) (Sort s)) $
        inferInternal s

-- | Given two types @a@ and @b@ with @a <: b@, check that @a == b@.
checkSubtypeIsEqual :: Type -> Type -> TCM ()
checkSubtypeIsEqual a b = do
  reportSDoc "tc.meta.subtype" 30 $
    "checking that subtype" <+> prettyTCM a <+>
    "of" <+> prettyTCM b <+> "is actually equal."
  SynEq.checkSyntacticEquality a b (\_ _ -> return ()) $ \a b -> do
    cumulativity <- optCumulativity <$> pragmaOptions
    abortIfBlocked (unEl b) >>= \case
      Sort sb -> abortIfBlocked (unEl a) >>= \case
        Sort sa | cumulativity -> equalSort sa sb
                             | otherwise    -> return ()
        Dummy{} -> return () -- TODO: this shouldn't happen but
                             -- currently does because of generalized
                             -- metas being created in a dummy context
        a -> patternViolation =<< updateBlocker (unblockOnAnyMetaIn a) -- TODO: can this happen?
      Pi b1 b2 -> abortIfBlocked (unEl a) >>= \case
        Pi a1 a2
          | getRelevance a1 /= getRelevance b1 -> patternViolation neverUnblock -- Can we recover from this?
          | getQuantity  a1 /= getQuantity  b1 -> patternViolation neverUnblock
          | getCohesion  a1 /= getCohesion  b1 -> patternViolation neverUnblock
          | getModalPolarity a1 /= getModalPolarity b1 -> patternViolation neverUnblock
          | otherwise -> do
              checkSubtypeIsEqual (unDom b1) (unDom a1)
              underAbstractionAbs a1 a2 $ \a2' -> checkSubtypeIsEqual a2' (absBody b2)
        Dummy{} -> return () -- TODO: this shouldn't happen but
                             -- currently does because of generalized
                             -- metas being created in a dummy context
        a -> patternViolation =<< updateBlocker (unblockOnAnyMetaIn a)
      -- TODO: check subtyping for Size< types
      _ -> return ()


-- | Turn the assignment problem @_X args <= SizeLt u@ into
-- @_X args = SizeLt (_Y args)@ and constraint
-- @_Y args <= u@.
subtypingForSizeLt
  :: CompareDirection -- ^ @dir@
  -> MetaId           -- ^ The local meta-variable @x@.
  -> MetaVariable     -- ^ Its associated information @mvar <- lookupLocalMeta x@.
  -> Type             -- ^ Its type @t = jMetaType $ mvJudgement mvar@
  -> Args             -- ^ Its arguments.
  -> Term             -- ^ Its to-be-assigned value @v@, such that @x args `dir` v@.
  -> (Term -> TCM ()) -- ^ Continuation taking its possibly assigned value.
  -> TCM ()
subtypingForSizeLt DirEq x mvar t args v cont = cont v
subtypingForSizeLt dir   x mvar t args v cont = do
  let fallback = cont v
  -- Check whether we have built-ins SIZE and SIZELT
  (mSize, mSizeLt) <- getBuiltinSize
  caseMaybe mSize   fallback $ \ qSize   -> do
    caseMaybe mSizeLt fallback $ \ qSizeLt -> do
      -- Check whether v is a SIZELT
      v <- reduce v
      case v of
        Def q [Apply (Arg ai u)] | q == qSizeLt -> do
          -- Clone the meta into a new size meta @y@.
          -- To this end, we swap the target of t for Size.
          TelV tel _ <- telView t
          let size = sizeType_ qSize
              t'   = telePi tel size
          y <- newMeta Instantiable (mvInfo mvar) (mvPriority mvar) (mvPermutation mvar)
                       (HasType __IMPOSSIBLE__ CmpLeq t')
          -- Note: no eta-expansion of new meta possible/necessary.
          -- Add the size constraint @y args `dir` u@.
          let yArgs = MetaV y $ map Apply args
          addConstraint (unblockOnMeta y) $ dirToCmp (`ValueCmp` AsSizes) dir yArgs u
          -- We continue with the new assignment problem, and install
          -- an exception handler, since we created a meta and a constraint,
          -- so we cannot fall back to the original handler.
          let xArgs = MetaV x $ map Apply args
              v'    = Def qSizeLt [Apply $ Arg ai yArgs]
              c     = dirToCmp (`ValueCmp` (AsTermsOf sizeUniv)) dir xArgs v'
          catchConstraint c $ cont v'
        _ -> fallback

-- | Eta-expand bound variables like @z@ in @X (fst z)@.
expandProjectedVars
  :: ( Pretty a, PrettyTCM a, NoProjectedVar a
     -- , Normalise a, TermLike a, Subst Term a
     , ReduceAndEtaContract a
     , PrettyTCM b, TermSubst b
     )
  => a  -- ^ Meta variable arguments.
  -> b  -- ^ Right hand side.
  -> (a -> b -> TCM c)
  -> TCM c
expandProjectedVars args v ret = loop (args, v) where
  loop (args, v) = do
    reportSDoc "tc.meta.assign.proj" 45 $ "meta args: " <+> prettyTCM args
    args <- callByName $ reduceAndEtaContract args
    reportSDoc "tc.meta.assign.proj" 45 $ "norm args: " <+> prettyTCM args
    reportSDoc "tc.meta.assign.proj" 85 $ "norm args: " <+> pretty args
    let done = ret args v
    case noProjectedVar args of
      Right ()              -> do
        reportSDoc "tc.meta.assign.proj" 40 $
          "no projected var found in args: " <+> prettyTCM args
        done
      Left (ProjectedVar i _) -> etaExpandProjectedVar i (args, v) done loop

-- | Eta-expand a de Bruijn index of record type in context and passed term(s).
etaExpandProjectedVar :: (PrettyTCM a, TermSubst a) => Int -> a -> TCM c -> (a -> TCM c) -> TCM c
etaExpandProjectedVar i v fail succeed = do
  reportSDoc "tc.meta.assign.proj" 40 $
    "trying to expand projected variable" <+> prettyTCM (var i)
  caseMaybeM (etaExpandBoundVar i) fail $ \ (delta, sigma, tau) -> do
    reportSDoc "tc.meta.assign.proj" 25 $
      "eta-expanding var " <+> prettyTCM (var i) <+>
      " in terms " <+> prettyTCM v
    unsafeInTopContext $ addContext delta $
      succeed $ applySubst tau v

-- | Check whether one of the meta args is a projected var.
class NoProjectedVar a where
  noProjectedVar :: a -> Either ProjectedVar ()

  default noProjectedVar
    :: (NoProjectedVar b, Foldable t, t b ~ a)
    => a -> Either ProjectedVar ()
  noProjectedVar = Fold.mapM_ noProjectedVar

instance NoProjectedVar a => NoProjectedVar (Arg a)
instance NoProjectedVar a => NoProjectedVar [a]

instance NoProjectedVar Term where
  noProjectedVar = \case
      Var i es
        | qs@(_:_) <- takeWhileJust id $ map isProjElim es
        -> Left $ ProjectedVar i qs
      -- Andreas, 2015-09-12 Issue #1316:
      -- Also look in inductive record constructors
      Con (ConHead _ IsRecord{} Inductive _) _ es
        | Just vs <- allApplyElims es
        -> noProjectedVar vs
      _ -> return ()

-- | Normalize just far enough to be able to eta-contract maximally.
class (TermLike a, TermSubst a, Reduce a) => ReduceAndEtaContract a where
  reduceAndEtaContract :: a -> TCM a

  default reduceAndEtaContract
    :: (Traversable f, TermLike b, Subst b, Reduce b, ReduceAndEtaContract b, f b ~ a)
    => a -> TCM a
  reduceAndEtaContract = Trav.mapM reduceAndEtaContract

instance ReduceAndEtaContract a => ReduceAndEtaContract [a]
instance ReduceAndEtaContract a => ReduceAndEtaContract (Arg a)

instance ReduceAndEtaContract Term where
  reduceAndEtaContract u = do
    reduce u >>= \case
      -- In case of lambda or record constructor, it makes sense to
      -- reduce further.
      Lam ai (Abs x b) -> etaLam ai x =<< reduceAndEtaContract b
      Con c ci es -> etaCon c ci es $ \ r c ci args -> do
        args <- reduceAndEtaContract args
        etaContractRecord r c ci args
      v -> return v

{- UNUSED, BUT KEEP!
-- Wrong attempt at expanding bound variables.
-- The following code curries meta instead.

-- | @etaExpandProjectedVar mvar x t n qs@
--
--   @mvar@ is the meta var info.
--   @x@ is the meta variable we are trying to solve for.
--   @t@ is its type.
--   @n@ is the number of the meta arg we want to curry (starting at 0).
--   @qs@ is the projection path along which we curry.
--
etaExpandProjectedVar :: MetaVariable -> MetaId -> Type -> Int -> [QName] -> TCM a
etaExpandProjectedVar mvar x t n qs = inTopContext $ do
  (_, uncurry, t') <- curryAt t n
  let TelV tel a = telView' t'
      perm       = idP (size tel)
  y <- newMeta (mvInfo mvar) (mvPriority mvar) perm (HasType __IMPOSSIBLE__ t')
  assignTerm' x (uncurry $ MetaV y [])
  patternViolation
-}

{-
  -- first, strip the leading n domains (which remain unchanged)
  TelV gamma core <- telViewUpTo n t
  case unEl core of
    -- There should be at least one domain left
    Pi (Dom ai a) b -> do
      -- Eta-expand @dom@ along @qs@ into a telescope @tel@, computing a substitution.
      -- For now, we only eta-expand once.
      -- This might trigger another call to @etaExpandProjectedVar@ later.
      -- A more efficient version does all the eta-expansions at once here.
      (r, pars, def) <- fromMaybe __IMPOSSIBLE__ <$> isRecordType a
      unless (recEtaEquality def) __IMPOSSIBLE__
      let tel = recTel def `apply` pars
          m   = size tel
          v   = Con (recConHead def) $ map var $ downFrom m
          b'  = raise m b `absApp` v
          fs  = recFields def
          vs  = zipWith (\ f i -> Var i [Proj f]) fs $ downFrom m
          -- v = c (n-1) ... 1 0
      (tel, u) <- etaExpandAtRecordType a $ var 0
      -- TODO: compose argInfo ai with tel.
      -- Substitute into @b@.
      -- Abstract over @tel@.
      -- Abstract over @gamma@.
      -- Create new meta.
      -- Solve old meta, using substitution.
      patternViolation
    _ -> __IMPOSSIBLE__
-}

type FVs = VarSet
type SubstCand = [(Int,Term)] -- ^ a possibly non-deterministic substitution

-- | Turn non-det substitution into proper substitution, if possible.
--   Otherwise, raise the error.
checkLinearity :: SubstCand -> ExceptT () TCM SubstCand
checkLinearity ids = do
  -- see issue #920
  List1.toList <$> mapM makeLinear (List1.groupOn fst ids)
  where
    -- Non-determinism can be healed if type is singleton. [Issue 593]
    -- (Same as for irrelevance.)
    makeLinear :: List1 (Int, Term) -> ExceptT () TCM (Int, Term)
    makeLinear (p       :| []) = return p
    makeLinear (p@(i,t) :| _ ) =
      ifM ((Right True ==) <$> do lift . runBlocked . isSingletonTypeModuloRelevance =<< typeOfBV i)
        (return p)
        (throwError ())

-- Intermediate result in the following function
type Res = [(Arg Nat, Term)]

-- | Exceptions raised when substitution cannot be inverted.
data InvertExcept
  = CantInvert Term           -- ^ Cannot recover.
  | NeutralArg                -- ^ A potentially neutral arg: can't invert, but can try pruning.
  | ProjVar ProjectedVar      -- ^ Try to eta-expand var to remove projs.

-- | Check that arguments @args@ to a metavar are in pattern fragment.
--   Assumes all arguments already in whnf and eta-reduced.
--   Parameters are represented as @Var@s so @checkArgs@ really
--   checks that all args are @Var@s and returns the "substitution"
--   to be applied to the rhs of the equation to solve.
--   (If @args@ is considered a substitution, its inverse is returned.)
--
--   The returned list might not be ordered.
--   Linearity, i.e., whether the substitution is deterministic,
--   has to be checked separately.
--
inverseSubst' :: (Term -> Bool) -> Args -> ExceptT InvertExcept TCM SubstCand
inverseSubst' skip args = map (mapFst unArg) <$> loop (zip args terms)
  where
  loop  = foldM isVarOrIrrelevant []
  terms = map var (downFrom (size args))
  failure c = do
    lift $ reportSDoc "tc.meta.assign" 15 $ vcat
      [ "not all arguments are variables: " <+> prettyTCM args
      , "  aborting assignment" ]
    throwError (CantInvert c)
  neutralArg = throwError NeutralArg

  isVarOrIrrelevant :: Res -> (Arg Term, Term) -> ExceptT InvertExcept TCM Res
  isVarOrIrrelevant vars (Arg info v, t) = do
    let irr | isIrrelevant info = True
            | DontCare{} <- v   = True
            | otherwise         = False
    ineg <- getPrimitiveName' builtinINeg
    case stripDontCare v of
      -- i := x
      Var i [] -> return $ (Arg info i, t) `cons` vars

      -- π i := x  try to eta-expand projection π away!
      Var i es | Just qs <- mapM isProjElim es ->
        throwError $ ProjVar $ ProjectedVar i qs

      -- (i, j) := x  becomes  [i := fst x, j := snd x]
      -- Andreas, 2013-09-17 but only if constructor is fully applied
      tm@(Con c ci es) -> do
        let fallback
             | isIrrelevant info = return vars
             | skip tm           = return vars
             | otherwise         = failure tm
        irrProj <- optIrrelevantProjections <$> pragmaOptions
        lift (isEtaRecordConstructor $ conName c) >>= \case
          -- Andreas, 2019-11-10, issue #4185: only for eta-records
          Just (_, RecordData{ _recFields = fs })
            | length fs == length es
            , hasQuantity0 info || all usableQuantity fs     -- Andreas, 2019-11-12/17, issue #4168b
            , irrProj || all isRelevant fs -> do
              let aux (Arg _ v) Dom{domInfo = info', unDom = f} =
                    (Arg ai v,) $ t `applyE` [Proj ProjSystem f]
                    where
                    ai = ArgInfo
                      { argInfoHiding   = min (getHiding info) (getHiding info')
                      , argInfoModality = Modality
                        { modRelevance  = max (getRelevance info) (getRelevance info')
                        , modQuantity   = max (getQuantity  info) (getQuantity  info')
                        , modCohesion   = max (getCohesion  info) (getCohesion  info')
                        , modPolarity   = addPolarity (getModalPolarity info) (getModalPolarity info') -- XXX
                        }
                      , argInfoOrigin   = min (getOrigin info) (getOrigin info')
                      , argInfoFreeVariables = unknownFreeVariables
                      , argInfoAnnotation    = argInfoAnnotation info'
                      }
                  vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
              res <- loop $ zipWith aux vs fs
              return $ res `append` vars
            | otherwise -> fallback
          _ -> fallback

      -- An irrelevant argument which is not an irrefutable pattern is dropped
      _ | irr -> return vars

      -- Distinguish args that can be eliminated (Con,Lit,Lam,unsure) ==> failure
      -- from those that can only put somewhere as a whole ==> neutralArg
      Var{}      -> neutralArg

      -- primINeg i := x becomes i := primINeg x
      -- (primINeg is a definitional involution)
      Def qn es | Just [Arg _ (Var i [])] <- allApplyElims es, Just qn == ineg ->
        pure $ (Arg info i, Def qn [Apply (defaultArg t)]) `cons` vars

      Def{}      -> neutralArg  -- Note that this Def{} is in normal form and might be prunable.
      t@Lam{}    -> failure t
      t@Lit{}    -> failure t
      t@MetaV{}  -> failure t
      Pi{}       -> neutralArg
      Sort{}     -> neutralArg
      Level{}    -> neutralArg
      DontCare{} -> __IMPOSSIBLE__ -- Ruled out by stripDontCare
      Dummy s _  -> __IMPOSSIBLE_VERBOSE__ s

  -- managing an assoc list where duplicate indizes cannot be irrelevant vars
  append :: Res -> Res -> Res
  append res vars = foldr cons vars res

  -- adding an irrelevant entry only if not present
  cons :: (Arg Nat, Term) -> Res -> Res
  cons a@(Arg ai i, t) vars
    | isIrrelevant ai = applyUnless (any ((i ==) . unArg . fst) vars) (a :) vars
    | otherwise       = a :  -- adding a relevant entry
        -- filter out duplicate irrelevants
        filter (not . (\ a@(Arg info j, t) -> isIrrelevant info && i == j)) vars

-- | If the given metavariable application represents a face, return:
--
--    * The metavariable information;
--    * The actual face, as an assignment of booleans to variables;
--
--    * The substitution candidate resulting from @inverseSubst'@. This
--    is guaranteed to be linear and deterministic.
--
--    * The actual substitution, mapping from the constraint context to
--    the metavariable's context.
--
--  Put concisely, a face constraint is an equation in the pattern
--  fragment modulo the presence of endpoints (@i0@ and @i1@) in the
--  telescope. In more detail, a face constraint has the form
--
--    @?0 Δ (i = i0) (j = i0) Γ (k = i1) Θ (l = i0) = t@
--
--  where all the greek letters consist entirely of distinct bound
--  variables (and, of course, arbitrarily many endpoints are allowed
--  between each substitution fragment).
isFaceConstraint
  :: MetaId
  -> Args
  -> TCM (Maybe (MetaVariable, IntMap.IntMap Bool, SubstCand, Substitution))
isFaceConstraint mid args = runMaybeT $ do
  iv   <- intervalView'
  mvar <- lookupLocalMeta mid  -- information associated with meta x
  -- Make sure that this is actually an interaction point:
  (_, _, _) <- MaybeT $ isInteractionMetaB mid args

  let
    t = jMetaType $ mvJudgement mvar
    n = length args

    isEndpoint tm = isJust (fin (defaultArg tm) 0)

    fin (Arg _ tm) i = case iv tm of
      IOne  -> Just (i, True)
      IZero -> Just (i, False)
      _     -> Nothing

  -- The logic here is essentially the same as for actually solving the
  -- meta.. We just return the pieces instead of doing the assignment.
  -- We must check the "face condition" (the relaxed pattern condition)
  -- and check linearity of the substitution candidate, otherwise the
  -- equation can't be inverted into a face constraint.
  sub <- MaybeT $ either (const Nothing) Just <$> runExceptT (inverseSubst' isEndpoint args)
  ids <- MaybeT $ either (const Nothing) Just <$> runExceptT (checkLinearity sub)

  m           <- getContextSize
  TelV tel' _ <- telViewUpToPath n t
  tel''       <- enterClosure mvar $ \_ -> getContextTelescope

  let
    assocToList i = \case
      _           | i >= m -> []
      ((j,u) : l) | i == j -> Just u  : assocToList (i + 1) l
      l                    -> Nothing : assocToList (i + 1) l
    ivs = assocToList 0 ids
    rho = prependS impossible ivs $ raiseS n

    over  = size tel' - size tel''
    endps = IntMap.fromList $ catMaybes $ zipWith (\a i -> fin a (i - over)) args (downFrom n)

  reportSDoc "tc.ip.boundary" 45 $ vcat
    [ "ivs   =" <+> prettyTCM ivs
    , "tel'  =" <+> prettyTCM tel'
    , "tel'' =" <+> prettyTCM tel''
    , "ids   =" <+> prettyTCM ids
    , "sub   =" <+> prettyTCM sub
    , "endps =" <+> pretty endps
    ]

  guard (not (IntMap.null endps))
  -- Can happen when the metavariable's context does not yet know about
  -- an interval variable it will be applied to later, eg in the partial
  -- argument to hcomp:
  guard (all (>= 0) (IntMap.keys endps))
  -- In that case we fail here — when the user writes some more
  -- patterns, they'll become positive
  pure (mvar, endps, ids, rho)

-- | Record a "face" equation onto an interaction point into the actual
-- interaction point boundary. Takes all the same arguments as
-- @assignMeta'@.
tryAddBoundary :: CompareDirection -> MetaId -> InteractionId -> Args -> Term -> CompareAs -> TCM ()
tryAddBoundary dir x iid args v target = do
  reportSDoc "tc.ip.boundary" 30 $ vcat
    [ "boundary: looking at equational constraint"
    , prettyTCM (MetaV x (Apply <$> args)) <+> "=?" <+> prettyTCM v
    ]
  iv   <- intervalView'
  mvar <- lookupLocalMeta x  -- information associated with meta x

  let
    t = jMetaType $ mvJudgement mvar
    n = length args
    rhsv = allFreeVars v

    allVars :: SubstCand -> Bool
    allVars sub = rhsv `VarSet.isSubsetOf` VarSet.fromList (map fst sub)

  TelV tel' _ <- telViewUpToPath n t

  void . runMaybeT $ do
    -- Make sure we're looking at a face constraint:
    (_, endps, ids, rho) <- MaybeT $ isFaceConstraint x args
    -- And that the non-endpoint parts of the 'Args' cover the free
    -- variables of the RHS:
    guard (allVars ids)

    -- ρ is a substitution from the "constraint context" (the context
    -- we're in) to the metavariable's context. moreover, v[ρ] is
    -- well-scoped in the meta's context.
    let v' = abstract tel' $ applySubst rho v
    -- We store the boundary faces directly as lambdas for simplicity.

    enterClosure mvar $ \_ -> do
      reportSDoc "tc.ip.boundary" 30 $ vcat
        [ "recovered interaction point boundary"
        , "  endps =" <+> pretty endps
        , "  rho   =" <+> pretty rho
        , "  t     =" <+> inTopContext (prettyTCM t)
        , "  v'    =" <+> inTopContext (prettyTCM v')
        ]

      let
        -- Always store the constraint with the smaller termSize:
        upd (IPBoundary m) = case MapS.lookup endps m of
          Just t -> if termSize t < termSize v'
            then IPBoundary m
            else IPBoundary $ MapS.insert endps v' m
          Nothing -> IPBoundary $ MapS.insert endps v' m
        f ip = ip{ ipBoundary = upd (ipBoundary ip) }

      lift $ modifyInteractionPoints (BiMap.adjust f iid)

-- | Turn open metas into postulates.
--
--   Preconditions:
--
--   1. We are 'inTopContext'.
--
--   2. 'envCurrentModule' is set to the top-level module.
--
openMetasToPostulates :: TCM ()
openMetasToPostulates = do
  m <- asksTC envCurrentModule

  -- Go through all open metas.
  ms <- MapS.assocs <$> useTC stOpenMetaStore
  forM_ ms $ \ (x, mv) -> do
    let t = dummyTypeToOmega $ jMetaType $ mvJudgement mv

    -- Create a name for the new postulate.
    let r = clValue $ miClosRange $ mvInfo mv
    s' <- render <$> prettyTCM x -- Using _ is a bad idea, as it prints as prefix op
    let s = "unsolved#meta." ++ filter (/= '_') s'
    n <- freshName r s
    let q = A.QName m n

    -- Debug.
    reportSDoc "meta.postulate" 20 $ vcat
      [ text ("Turning " ++ if isSortMeta_ mv then "sort" else "value" ++ " meta ")
          <+> prettyTCM x <+> " into postulate."
      , nest 2 $ vcat
        [ "Name: " <+> prettyTCM q
        , "Type: " <+> prettyTCM t
        ]
      ]

    -- Add the new postulate to the signature.
    addConstant' q defaultArgInfo t defaultAxiom

    -- Solve the meta.
    let inst = InstV $ Instantiation
                 { instTel = [], instBody = Def q [] }
    updateMetaVar x $ \ mv0 -> mv0 { mvInstantiation = inst }
    return ()
  where
    -- Unsolved sort metas can have a type ending in a Dummy if they are allowed to be instantiated
    -- to Setω. This will crash the serializer (issue #3730). To avoid this we replace dummy type
    -- codomains by Setω.
    dummyTypeToOmega t =
      case telView' t of
        TelV tel (El _ Dummy{}) -> abstract tel (sort $ Inf UType 0)
        _ -> t

-- | Sort metas in dependency order.
dependencySortMetas :: [MetaId] -> TCM (Maybe [MetaId])
dependencySortMetas metas = do
  metaGraph <- concat <$> do
    forM metas $ \ m -> do
      deps <- allMetas (\m' -> if m' `Set.member` metas'
                               then singleton m'
                               else mempty) <$>
                getType m
      return [ (m, m') | m' <- Set.toList deps ]

  return $ Graph.topSort metas' metaGraph

  where
    metas' = Set.fromList metas

    -- Sort metas don't have types, but we still want to sort them.
    getType m = do
      j <- lookupMetaJudgement m
      case j of
        IsSort{}                 -> return Nothing
        HasType{ jMetaType = t } -> Just <$> instantiateFull t

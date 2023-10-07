{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Monad.MetaVars where

import Prelude hiding (null)

import Control.Monad                ( (<=<), forM_, guard )
import Control.Monad.Except         ( MonadError )
import Control.Monad.State          ( StateT, execStateT, get, put )
import Control.Monad.Trans          ( MonadTrans, lift )
import Control.Monad.Trans.Identity ( IdentityT )
import Control.Monad.Reader         ( ReaderT(ReaderT), runReaderT )
import Control.Monad.Writer         ( WriterT, execWriterT, tell )
-- Control.Monad.Fail import is redundant since GHC 8.8.1
import Control.Monad.Fail (MonadFail)

import qualified Data.HashMap.Strict as HMap
import qualified Data.List as List
import qualified Data.Map.Strict as MapS
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Foldable as Fold

import GHC.Stack (HasCallStack)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Common.Pretty (prettyShow)

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin (HasBuiltins)
import Agda.TypeChecking.Monad.Trace
import Agda.TypeChecking.Monad.Closure
import Agda.TypeChecking.Monad.Constraints (MonadConstraint(..))
import Agda.TypeChecking.Monad.Debug
  (MonadDebug, reportSLn, __IMPOSSIBLE_VERBOSE__)
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Signature (HasConstInfo)
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Substitute
import {-# SOURCE #-} Agda.TypeChecking.Telescope

import qualified Agda.Utils.BiMap as BiMap
import Agda.Utils.Functor ((<.>))
import Agda.Utils.Lens
import Agda.Utils.List (nubOn)
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Tuple
import qualified Agda.Utils.Maybe.Strict as Strict

import Agda.Utils.Impossible

-- | Various kinds of metavariables.

data MetaKind =
    Records
    -- ^ Meta variables of record type.
  | SingletonRecords
    -- ^ Meta variables of \"hereditarily singleton\" record type.
  | Levels
    -- ^ Meta variables of level type, if type-in-type is activated.
  deriving (Eq, Enum, Bounded, Show)

-- | All possible metavariable kinds.

allMetaKinds :: [MetaKind]
allMetaKinds = [minBound .. maxBound]

data KeepMetas = KeepMetas | RollBackMetas

-- | Monad service class for creating, solving and eta-expanding of
--   metavariables.
class ( MonadConstraint m
      , MonadReduce m
      , MonadAddContext m
      , MonadTCEnv m
      , ReadTCState m
      , HasBuiltins m
      , HasConstInfo m
      , MonadDebug m
      ) => MonadMetaSolver m where
  -- | Generate a new meta variable with some instantiation given.
  --   For instance, the instantiation could be a 'PostponedTypeCheckingProblem'.
  newMeta' :: MetaInstantiation -> Frozen -> MetaInfo -> MetaPriority -> Permutation ->
              Judgement a -> m MetaId

  -- * Solve constraint @x vs = v@.

  -- | Assign to an open metavar which may not be frozen.
  --   First check that metavar args are in pattern fragment.
  --     Then do extended occurs check on given thing.
  --
  --   Assignment is aborted by throwing a @PatternErr@ via a call to
  --   @patternViolation@.  This error is caught by @catchConstraint@
  --   during equality checking (@compareAtom@) and leads to
  --   restoration of the original constraints.
  assignV :: CompareDirection -> MetaId -> Args -> Term -> CompareAs -> m ()

  -- | Directly instantiate the metavariable. Skip pattern check,
  -- occurs check and frozen check. Used for eta expanding frozen
  -- metas.
  assignTerm' :: MonadMetaSolver m => MetaId -> [Arg ArgName] -> Term -> m ()

  -- | Eta-expand a local meta-variable, if it is of the specified
  -- kind. Don't do anything if the meta-variable is a blocked term.
  etaExpandMeta :: [MetaKind] -> MetaId -> m ()

  -- | Update the status of the metavariable
  updateMetaVar :: MetaId -> (MetaVariable -> MetaVariable) -> m ()

  -- | 'speculateMetas fallback m' speculatively runs 'm', but if the
  --    result is 'RollBackMetas' any changes to metavariables are
  --    rolled back and 'fallback' is run instead.
  speculateMetas :: m () -> m KeepMetas -> m ()

instance MonadMetaSolver m => MonadMetaSolver (ReaderT r m) where
  newMeta' inst f i p perm j = lift $ newMeta' inst f i p perm j
  assignV dir m us v cmp = lift $ assignV dir m us v cmp
  assignTerm' m us v = lift $ assignTerm' m us v
  etaExpandMeta k m = lift $ etaExpandMeta k m
  updateMetaVar m f = lift $ updateMetaVar m f
  speculateMetas fallback m = ReaderT $ \x -> speculateMetas (runReaderT fallback x) (runReaderT m x)

-- | Switch off assignment of metas.
dontAssignMetas :: (MonadTCEnv m, HasOptions m, MonadDebug m) => m a -> m a
dontAssignMetas cont = do
  reportSLn "tc.meta" 45 $ "don't assign metas"
  localTC (\ env -> env { envAssignMetas = False }) cont

-- | Is the meta-variable from another top-level module?

isRemoteMeta :: ReadTCState m => m (MetaId -> Bool)
isRemoteMeta = do
  h <- currentModuleNameHash
  return (\m -> h /= metaModule m)

-- | If another meta-variable is created, then it will get this
-- 'MetaId' (unless the state is changed too much, for instance by
-- 'setTopLevelModule').

nextLocalMeta :: ReadTCState m => m MetaId
nextLocalMeta = useR stFreshMetaId

-- | Pairs of local meta-stores.

data LocalMetaStores = LocalMetaStores
  { openMetas :: LocalMetaStore
    -- ^ A 'MetaStore' containing open meta-variables.
  , solvedMetas :: LocalMetaStore
    -- ^ A 'MetaStore' containing instantiated meta-variables.
  }

-- | Run a computation and record which new metas it created.
metasCreatedBy ::
  forall m a. ReadTCState m => m a -> m (a, LocalMetaStores)
metasCreatedBy m = do
  !nextMeta <- nextLocalMeta
  a         <- m
  os        <- created stOpenMetaStore   nextMeta
  ss        <- created stSolvedMetaStore nextMeta
  return (a, LocalMetaStores { openMetas = os, solvedMetas = ss })
  where
  created :: Lens' TCState LocalMetaStore -> MetaId -> m LocalMetaStore
  created store next = do
    ms <- useTC store
    return $ case MapS.splitLookup next ms of
      (_, Nothing, ms) -> ms
      (_, Just m,  ms) -> MapS.insert next m ms

-- | Find information about the given local meta-variable, if any.

lookupLocalMeta' :: ReadTCState m => MetaId -> m (Maybe MetaVariable)
lookupLocalMeta' m = do
  mv <- lkup <$> useR stSolvedMetaStore
  case mv of
    mv@Just{} -> return mv
    Nothing   -> lkup <$> useR stOpenMetaStore
  where
  lkup = MapS.lookup m

-- | Find information about the given local meta-variable.

lookupLocalMeta ::
  (HasCallStack, MonadDebug m, ReadTCState m) =>
  MetaId -> m MetaVariable
lookupLocalMeta m =
  fromMaybeM (__IMPOSSIBLE_VERBOSE__ err) $ lookupLocalMeta' m
  where
  err = "no such local meta-variable " ++ prettyShow m

-- | Find information about the (local or remote) meta-variable, if
-- any.
--
-- If no meta-variable is found, then the reason could be that the
-- dead-code elimination
-- ('Agda.TypeChecking.DeadCode.eliminateDeadCode') failed to find the
-- meta-variable, perhaps because some 'NamesIn' instance is
-- incorrectly defined.

{-# SPECIALIZE lookupMeta :: MetaId -> TCM (Maybe (Either RemoteMetaVariable MetaVariable)) #-}
lookupMeta ::
  ReadTCState m =>
  MetaId -> m (Maybe (Either RemoteMetaVariable MetaVariable))
lookupMeta m = do
  mv <- lookupLocalMeta' m
  case mv of
    Just mv -> return (Just (Right mv))
    Nothing -> fmap Left . HMap.lookup m <$> useR stImportedMetaStore

-- | Find the meta-variable's instantiation.

{-# SPECIALIZE lookupMetaInstantiation :: MetaId -> TCM MetaInstantiation #-}
lookupMetaInstantiation ::
  ReadTCState m => MetaId -> m MetaInstantiation
lookupMetaInstantiation m = do
  mi <- lookupMeta m
  case mi of
    Just (Left mv)  -> return (InstV $ rmvInstantiation mv)
    Just (Right mv) -> return (mvInstantiation mv)
    Nothing         -> __IMPOSSIBLE__

-- | Find the meta-variable's judgement.

lookupMetaJudgement :: ReadTCState m => MetaId -> m (Judgement MetaId)
lookupMetaJudgement m = do
  mi <- lookupMeta m
  case mi of
    Just (Left mv)  -> return (rmvJudgement mv)
    Just (Right mv) -> return (mvJudgement mv)
    Nothing         -> __IMPOSSIBLE__

-- | Find the meta-variable's modality.

lookupMetaModality :: ReadTCState m => MetaId -> m Modality
lookupMetaModality m = do
  mi <- lookupMeta m
  case mi of
    Just (Left mv)  -> return (rmvModality mv)
    Just (Right mv) -> return (getModality mv)
    Nothing         -> __IMPOSSIBLE__

{-# INLINE metaType #-}
-- | The type of a term or sort meta-variable.
metaType :: ReadTCState m => MetaId -> m Type
metaType x = jMetaType <$> lookupMetaJudgement x

-- | Update the information associated with a local meta-variable.
updateMetaVarTCM ::
  HasCallStack => MetaId -> (MetaVariable -> MetaVariable) -> TCM ()
updateMetaVarTCM m f = do
  mv <- lookupLocalMeta' m
  case mv of
    Nothing -> do
      mv <- lookupMeta m
      case mv of
        Nothing -> __IMPOSSIBLE_VERBOSE__
                     ("Meta-variable not found: " ++ prettyShow m)
        Just{}  -> __IMPOSSIBLE_VERBOSE__
                     ("Attempt to update remote meta-variable: " ++
                      prettyShow m)
    Just mv -> do
      let mv'    = f mv
          insert = (`modifyTCLens` MapS.insert m mv')
          delete = (`modifyTCLens` MapS.delete m)
      case ( isOpenMeta (mvInstantiation mv)
           , isOpenMeta (mvInstantiation mv')
           ) of
        (True,  True)  -> insert stOpenMetaStore
        (False, False) -> insert stSolvedMetaStore
        (True,  False) -> do
          delete stOpenMetaStore
          insert stSolvedMetaStore
        (False, True)  -> __IMPOSSIBLE__

-- | Insert a new meta-variable with associated information into the
-- local meta store.
insertMetaVar :: MetaId -> MetaVariable -> TCM ()
insertMetaVar m mv
  | isOpenMeta (mvInstantiation mv) = insert stOpenMetaStore
  | otherwise                       = insert stSolvedMetaStore
  where
  insert = (`modifyTCLens` MapS.insert m mv)

{-# INLINE getMetaPriority #-}
-- | Returns the 'MetaPriority' of the given local meta-variable.
getMetaPriority ::
  (HasCallStack, MonadDebug m, ReadTCState m) =>
  MetaId -> m MetaPriority
getMetaPriority = mvPriority <.> lookupLocalMeta

isSortMeta :: ReadTCState m => MetaId -> m Bool
isSortMeta m = isSortJudgement <$> lookupMetaJudgement m

isSortMeta_ :: MetaVariable -> Bool
isSortMeta_ mv = isSortJudgement (mvJudgement mv)

isSortJudgement :: Judgement a -> Bool
isSortJudgement HasType{} = False
isSortJudgement IsSort{}  = True

{-# SPECIALIZE getMetaType :: MetaId -> TCM Type #-}
getMetaType :: ReadTCState m => MetaId -> m Type
getMetaType m = do
  j <- lookupMetaJudgement m
  return $ case j of
    HasType{ jMetaType = t } -> t
    IsSort{}  -> __IMPOSSIBLE__

{-# SPECIALIZE getMetaContextArgs :: MetaVariable -> TCM Args #-}
-- | Compute the context variables that a local meta-variable should
-- be applied to, accounting for pruning.
getMetaContextArgs :: MonadTCEnv m => MetaVariable -> m Args
getMetaContextArgs MetaVar{ mvPermutation = p } = do
  args <- getContextArgs
  return $ permute (takeP (length args) p) args

{-# SPECIALIZE getMetaTypeInContext :: MetaId -> TCM Type #-}
-- | Given a local meta-variable, return the type applied to the
-- current context.
getMetaTypeInContext ::
  (HasBuiltins m, HasCallStack, MonadDebug m, MonadReduce m,
   MonadTCEnv m, ReadTCState m) =>
  MetaId -> m Type
getMetaTypeInContext m = do
  mv@MetaVar{ mvJudgement = j } <- lookupLocalMeta m
  case j of
    HasType{ jMetaType = t } -> piApplyM t =<< getMetaContextArgs mv
    IsSort{}                 -> __IMPOSSIBLE__

{-# SPECIALIZE isGeneralizableMeta :: MetaId -> TCM DoGeneralize #-}
-- | Is it a local meta-variable that might be generalized?
isGeneralizableMeta ::
  (HasCallStack, MonadDebug m, ReadTCState m) =>
  MetaId -> m DoGeneralize
isGeneralizableMeta x =
  unArg . miGeneralizable . mvInfo <$> lookupLocalMeta x

-- | Check whether all metas are instantiated.
--   Precondition: argument is a meta (in some form) or a list of metas.
class IsInstantiatedMeta a where
  isInstantiatedMeta :: (MonadFail m, ReadTCState m) => a -> m Bool

{-# SPECIALIZE isInstantiatedMeta :: Term -> TCM Bool #-}
{-# SPECIALIZE isInstantiatedMeta :: Type -> TCM Bool #-}

instance IsInstantiatedMeta MetaId where
  isInstantiatedMeta m = isJust <$> isInstantiatedMeta' m

instance IsInstantiatedMeta Term where
  isInstantiatedMeta = loop where
   loop v =
    case v of
      MetaV x _  -> isInstantiatedMeta x
      DontCare v -> loop v
      Level l    -> isInstantiatedMeta l
      Lam _ b    -> isInstantiatedMeta b
      Con _ _ es | Just vs <- allApplyElims es -> isInstantiatedMeta vs
      _          -> __IMPOSSIBLE__

instance IsInstantiatedMeta Level where
  isInstantiatedMeta (Max n ls) | n == 0 = isInstantiatedMeta ls
  isInstantiatedMeta _ = __IMPOSSIBLE__

instance IsInstantiatedMeta PlusLevel where
  isInstantiatedMeta (Plus n l) | n == 0 = isInstantiatedMeta l
  isInstantiatedMeta _ = __IMPOSSIBLE__

instance IsInstantiatedMeta a => IsInstantiatedMeta [a] where
  isInstantiatedMeta = andM . map isInstantiatedMeta

instance IsInstantiatedMeta a => IsInstantiatedMeta (Maybe a) where
  isInstantiatedMeta = isInstantiatedMeta . maybeToList

instance IsInstantiatedMeta a => IsInstantiatedMeta (Arg a) where
  isInstantiatedMeta = isInstantiatedMeta . unArg

-- | Does not worry about raising.
instance IsInstantiatedMeta a => IsInstantiatedMeta (Abs a) where
  isInstantiatedMeta = isInstantiatedMeta . unAbs

{-# SPECIALIZE isInstantiatedMeta' :: MetaId -> TCM (Maybe Term) #-}
isInstantiatedMeta' :: (MonadFail m, ReadTCState m) => MetaId -> m (Maybe Term)
isInstantiatedMeta' m = do
  inst <- lookupMetaInstantiation m
  return $ case inst of
    InstV inst -> Just $ foldr mkLam (instBody inst) (instTel inst)
    _          -> Nothing

-- | Returns all metavariables in a constraint. Slightly complicated by the
--   fact that blocked terms are represented by two meta variables. To find the
--   second one we need to look up the meta listeners for the one in the
--   UnBlock constraint.
--   This is used for the purpose of deciding if a metavariable is constrained or if it can be
--   generalized over (see Agda.TypeChecking.Generalize).
constraintMetas :: Constraint -> TCM (Set MetaId)
constraintMetas = \case
    -- We don't use allMetas here since some constraints should not stop us from generalizing. For
    -- instance CheckSizeLtSat (see #3694). We also have to check meta listeners to get metas of
    -- UnBlock constraints.
    -- #5147: Don't count metas in the type of a constraint. For instance the constraint u = v : t
    -- should not stop us from generalize metas in t, since we could never solve those metas based
    -- on that constraint alone.
      ValueCmp _ _ u v         -> return $ allMetas Set.singleton (u, v)
      ValueCmpOnFace _ p _ u v -> return $ allMetas Set.singleton (p, u, v)
      ElimCmp _ _ _ _ es es'   -> return $ allMetas Set.singleton (es, es')
      LevelCmp _ l l'          -> return $ allMetas Set.singleton (Level l, Level l')
      UnquoteTactic t h g      -> return $ allMetas Set.singleton (t, h, g)
      SortCmp _ s1 s2          -> return $ allMetas Set.singleton (Sort s1, Sort s2)
      UnBlock x                -> Set.insert x . Set.unions <$> (mapM listenerMetas =<< getMetaListeners x)
      FindInstance x _         ->
        -- #5093: We should not generalize over metas bound by instance constraints.
        -- We keep instance constraints even if the meta is solved, to check that it could indeed
        -- be filled by instance search. If it's solved, look in the solution.
        caseMaybeM (isInstantiatedMeta' x) (return $ Set.singleton x) $ return . allMetas Set.singleton
      IsEmpty{}                -> return mempty
      CheckFunDef{}            -> return mempty
      CheckSizeLtSat{}         -> return mempty
      HasBiggerSort{}          -> return mempty
      HasPTSRule{}             -> return mempty
      CheckDataSort{}          -> return mempty
      CheckMetaInst x          -> return mempty
      CheckType t              -> return $ allMetas Set.singleton t
      CheckLockedVars a b c d  -> return $ allMetas Set.singleton (a, b, c, d)
      UsableAtModality{}       -> return mempty
  where
    -- For blocked constant twin variables
    listenerMetas EtaExpand{}           = return Set.empty
    listenerMetas (CheckConstraint _ c) = constraintMetas (clValue $ theConstraint c)

-- | Create 'MetaInfo' in the current environment.
createMetaInfo :: (MonadTCEnv m, ReadTCState m) => m MetaInfo
createMetaInfo = createMetaInfo' RunMetaOccursCheck

createMetaInfo'
  :: (MonadTCEnv m, ReadTCState m)
  => RunMetaOccursCheck -> m MetaInfo
createMetaInfo' b = do
  r        <- getCurrentRange
  cl       <- buildClosure r
  gen      <- viewTC eGeneralizeMetas
  modality <- currentModality
  return MetaInfo
    { miClosRange       = cl
    , miModality        = modality
    , miMetaOccursCheck = b
    , miNameSuggestion  = ""
    , miGeneralizable   = defaultArg gen
                          -- The ArgInfo is set to the right value in
                          -- the newArgsMetaCtx' function.
    }

setValueMetaName :: MonadMetaSolver m => Term -> MetaNameSuggestion -> m ()
setValueMetaName v s = do
  case v of
    MetaV mi _ -> setMetaNameSuggestion mi s
    u          -> do
      reportSLn "tc.meta.name" 70 $
        "cannot set meta name; newMeta returns " ++ show u
      return ()

getMetaNameSuggestion ::
  (HasCallStack, MonadDebug m, ReadTCState m) =>
  MetaId -> m MetaNameSuggestion
getMetaNameSuggestion mi =
  miNameSuggestion . mvInfo <$> lookupLocalMeta mi

setMetaNameSuggestion :: MonadMetaSolver m => MetaId -> MetaNameSuggestion -> m ()
setMetaNameSuggestion mi s = unless (null s || isUnderscore s) $ do
  reportSLn "tc.meta.name" 20 $
    "setting name of meta " ++ prettyShow mi ++ " to " ++ s
  updateMetaVar mi $ \ mvar ->
    mvar { mvInfo = (mvInfo mvar) { miNameSuggestion = s }}

-- | Change the ArgInfo that will be used when generalizing over this
-- local meta-variable.
setMetaGeneralizableArgInfo :: MonadMetaSolver m => MetaId -> ArgInfo -> m ()
setMetaGeneralizableArgInfo m i = updateMetaVar m $ \ mv ->
  mv { mvInfo = (mvInfo mv)
        { miGeneralizable = setArgInfo i (miGeneralizable (mvInfo mv)) } }

updateMetaVarRange :: MonadMetaSolver m => MetaId -> Range -> m ()
updateMetaVarRange mi r = updateMetaVar mi (setRange r)

setMetaOccursCheck :: MonadMetaSolver m => MetaId -> RunMetaOccursCheck -> m ()
setMetaOccursCheck mi b = updateMetaVar mi $ \ mvar ->
  mvar { mvInfo = (mvInfo mvar) { miMetaOccursCheck = b } }

-- * Query and manipulate interaction points.

class (MonadTCEnv m, ReadTCState m) => MonadInteractionPoints m where
  freshInteractionId :: m InteractionId
  default freshInteractionId
    :: (MonadTrans t, MonadInteractionPoints n, t n ~ m)
    => m InteractionId
  freshInteractionId = lift freshInteractionId

  modifyInteractionPoints :: (InteractionPoints -> InteractionPoints) -> m ()
  default modifyInteractionPoints
    :: (MonadTrans t, MonadInteractionPoints n, t n ~ m)
    => (InteractionPoints -> InteractionPoints) -> m ()
  modifyInteractionPoints = lift . modifyInteractionPoints

instance MonadInteractionPoints m => MonadInteractionPoints (IdentityT m)
instance MonadInteractionPoints m => MonadInteractionPoints (ReaderT r m)
instance MonadInteractionPoints m => MonadInteractionPoints (StateT s m)

instance MonadInteractionPoints TCM where
  freshInteractionId = fresh
  modifyInteractionPoints f = stInteractionPoints `modifyTCLens` f

-- | Register an interaction point during scope checking.
--   If there is no interaction id yet, create one.
registerInteractionPoint
  :: forall m. MonadInteractionPoints m
  => Bool -> Range -> Maybe Nat -> m InteractionId
registerInteractionPoint preciseRange r maybeId = do
  m <- useR stInteractionPoints
  -- If we're given an interaction id we shouldn't look up by range.
  -- This is important when doing 'refine', since all interaction points
  -- created by the refine gets the same range.
  if not preciseRange || isJust maybeId then continue m else do
    -- If the range does not come from a file, it is not
    -- precise, so ignore it.
    Strict.caseMaybe (rangeFile r) (continue m) $ \ _ -> do
    -- First, try to find the interaction point by Range.
    caseMaybe (findInteractionPoint_ r m) (continue m) {-else-} return
 where
 continue :: InteractionPoints -> m InteractionId
 continue m = do
  -- We did not find an interaction id with the same Range, so let's create one!
  ii <- case maybeId of
    Just i  -> return $ InteractionId i
    Nothing -> freshInteractionId
  let ip = InteractionPoint { ipRange = r, ipMeta = Nothing, ipSolved = False, ipClause = IPNoClause, ipBoundary = IPBoundary mempty }
  case BiMap.insertLookupWithKey (\ key new old -> old) ii ip m of
    -- If the interaction point is already present, we keep the old ip.
    -- However, it needs to be at the same range as the new one.
    (Just ip0, _)
       | ipRange ip /= ipRange ip0 -> __IMPOSSIBLE__
       | otherwise                 -> return ii
    (Nothing, m') -> do
      modifyInteractionPoints (const m')
      return ii

-- | Find an interaction point by 'Range' by searching the whole map.
--   Issue 3000: Don't consider solved interaction points.
--
--   O(n): linear in the number of registered interaction points.

findInteractionPoint_ :: Range -> InteractionPoints -> Maybe InteractionId
findInteractionPoint_ r m = do
  guard $ not $ null r
  listToMaybe $ mapMaybe sameRange $ BiMap.toList m
  where
    sameRange :: (InteractionId, InteractionPoint) -> Maybe InteractionId
    sameRange (ii, InteractionPoint r' _ False _ _) | r == r' = Just ii
    sameRange _ = Nothing

{-# INLINABLE connectInteractionPoint #-}
-- | Hook up a local meta-variable to an interaction point.
connectInteractionPoint
  :: MonadInteractionPoints m
  => InteractionId -> MetaId -> m ()
connectInteractionPoint ii mi = do
  ipCl <- asksTC envClause
  m <- useR stInteractionPoints
  let ip = InteractionPoint { ipRange = __IMPOSSIBLE__, ipMeta = Just mi, ipSolved = False, ipClause = ipCl, ipBoundary = IPBoundary mempty }
  -- The interaction point needs to be present already, we just set the meta.
  case BiMap.insertLookupWithKey (\ key new old -> new { ipRange = ipRange old }) ii ip m of
    (Nothing, _) -> __IMPOSSIBLE__
    (Just _, m') -> modifyInteractionPoints $ const m'

-- | Mark an interaction point as solved.
removeInteractionPoint :: MonadInteractionPoints m => InteractionId -> m ()
removeInteractionPoint ii =
  modifyInteractionPoints $ BiMap.update (\ ip -> Just ip{ ipSolved = True }) ii

-- | Get a list of interaction ids.
{-# SPECIALIZE getInteractionPoints :: TCM [InteractionId] #-}
getInteractionPoints :: ReadTCState m => m [InteractionId]
getInteractionPoints = BiMap.keys <$> useR stInteractionPoints

-- | Get all metas that correspond to unsolved interaction ids.
getInteractionMetas :: ReadTCState m => m [MetaId]
getInteractionMetas =
  mapMaybe ipMeta . filter (not . ipSolved) . BiMap.elems <$> useR stInteractionPoints

getUniqueMetasRanges ::
  (HasCallStack, MonadDebug m, ReadTCState m) => [MetaId] -> m [Range]
getUniqueMetasRanges = fmap (nubOn id) . mapM getMetaRange

getUnsolvedMetas ::
  (HasCallStack, MonadDebug m, ReadTCState m) => m [Range]
getUnsolvedMetas = do
  openMetas            <- getOpenMetas
  interactionMetas     <- getInteractionMetas
  getUniqueMetasRanges (openMetas List.\\ interactionMetas)

getUnsolvedInteractionMetas ::
  (HasCallStack, MonadDebug m, ReadTCState m) => m [Range]
getUnsolvedInteractionMetas = getUniqueMetasRanges =<< getInteractionMetas

-- | Get all metas that correspond to unsolved interaction ids.
getInteractionIdsAndMetas :: ReadTCState m => m [(InteractionId,MetaId)]
getInteractionIdsAndMetas =
  mapMaybe f . filter (not . ipSolved . snd) . BiMap.toList <$> useR stInteractionPoints
  where f (ii, ip) = (ii,) <$> ipMeta ip

-- | Does the meta variable correspond to an interaction point?
--
--   Time: @O(log n)@ where @n@ is the number of interaction metas.
isInteractionMeta :: ReadTCState m => MetaId -> m (Maybe InteractionId)
isInteractionMeta x = BiMap.invLookup x <$> useR stInteractionPoints

-- | Get the information associated to an interaction point.
{-# SPECIALIZE lookupInteractionPoint :: InteractionId -> TCM InteractionPoint #-}
lookupInteractionPoint
  :: (MonadFail m, ReadTCState m, MonadError TCErr m)
  => InteractionId -> m InteractionPoint
lookupInteractionPoint ii =
  fromMaybeM err $ BiMap.lookup ii <$> useR stInteractionPoints
  where
    err  = fail $ "no such interaction point: " ++ show ii

{-# SPECIALIZE lookupInteractionId :: InteractionId -> TCM MetaId #-}
-- | Get 'MetaId' for an interaction point.
--   Precondition: interaction point is connected.
lookupInteractionId
  :: (MonadFail m, ReadTCState m, MonadError TCErr m, MonadTCEnv m)
  => InteractionId -> m MetaId
lookupInteractionId ii = fromMaybeM err2 $ ipMeta <$> lookupInteractionPoint ii
  where
    err2 = typeError $ GenericError $ "No type nor action available for hole " ++ prettyShow ii ++ ". Possible cause: the hole has not been reached during type checking (do you see yellow?)"

-- | Check whether an interaction id is already associated with a meta variable.
lookupInteractionMeta :: ReadTCState m => InteractionId -> m (Maybe MetaId)
lookupInteractionMeta ii = lookupInteractionMeta_ ii <$> useR stInteractionPoints

lookupInteractionMeta_ :: InteractionId -> InteractionPoints -> Maybe MetaId
lookupInteractionMeta_ ii m = ipMeta =<< BiMap.lookup ii m

-- | Generate new meta variable.
newMeta :: MonadMetaSolver m => Frozen -> MetaInfo -> MetaPriority -> Permutation -> Judgement a -> m MetaId
newMeta = newMeta' Open

-- | Generate a new meta variable with some instantiation given.
--   For instance, the instantiation could be a 'PostponedTypeCheckingProblem'.
newMetaTCM' :: MetaInstantiation -> Frozen -> MetaInfo -> MetaPriority -> Permutation ->
               Judgement a -> TCM MetaId
newMetaTCM' inst frozen mi p perm j = do
  x <- fresh
  let j' = j { jMetaId = x }  -- fill the identifier part of the judgement
      mv = MetaVar{ mvInfo             = mi
                  , mvPriority         = p
                  , mvPermutation      = perm
                  , mvJudgement        = j'
                  , mvInstantiation    = inst
                  , mvListeners        = Set.empty
                  , mvFrozen           = frozen
                  , mvTwin             = Nothing
                  }
  -- printing not available (import cycle)
  -- reportSDoc "tc.meta.new" 50 $ "new meta" <+> prettyTCM j'
  insertMetaVar x mv
  return x

-- | Get the 'Range' for an interaction point.
{-# SPECIALIZE getInteractionRange :: InteractionId -> TCM Range #-}
getInteractionRange
  :: (MonadInteractionPoints m, MonadFail m, MonadError TCErr m)
  => InteractionId -> m Range
getInteractionRange = ipRange <.> lookupInteractionPoint

-- | Get the 'Range' for a local meta-variable.
getMetaRange ::
  (HasCallStack, MonadDebug m, ReadTCState m) => MetaId -> m Range
getMetaRange = getRange <.> lookupLocalMeta

getInteractionScope ::
  (MonadDebug m, MonadFail m, ReadTCState m, MonadError TCErr m,
   MonadTCEnv m) =>
  InteractionId -> m ScopeInfo
getInteractionScope =
  getMetaScope <.> lookupLocalMeta <=< lookupInteractionId

withMetaInfo' :: (MonadTCEnv m, ReadTCState m, MonadTrace m) => MetaVariable -> m a -> m a
withMetaInfo' mv = withMetaInfo (miClosRange $ mvInfo mv)

withMetaInfo :: (MonadTCEnv m, ReadTCState m, MonadTrace m) => Closure Range -> m a -> m a
withMetaInfo mI cont = enterClosure mI $ \ r ->
  setCurrentRange r cont

withInteractionId ::
  (MonadDebug m, MonadFail m, ReadTCState m, MonadError TCErr m,
   MonadTCEnv m, MonadTrace m) =>
  InteractionId -> m a -> m a
withInteractionId i ret = do
  m <- lookupInteractionId i
  withMetaId m ret

withMetaId ::
  (HasCallStack, MonadDebug m, MonadTCEnv m, MonadTrace m,
   ReadTCState m) =>
  MetaId -> m a -> m a
withMetaId m ret = do
  mv <- lookupLocalMeta m
  withMetaInfo' mv ret

getOpenMetas :: ReadTCState m => m [MetaId]
getOpenMetas = MapS.keys <$> useR stOpenMetaStore

isOpenMeta :: MetaInstantiation -> Bool
isOpenMeta Open                           = True
isOpenMeta OpenInstance                   = True
isOpenMeta BlockedConst{}                 = True
isOpenMeta PostponedTypeCheckingProblem{} = True
isOpenMeta InstV{}                        = False

-- | @listenToMeta l m@: register @l@ as a listener to @m@. This is done
--   when the type of l is blocked by @m@.
listenToMeta :: MonadMetaSolver m => Listener -> MetaId -> m ()
listenToMeta l m =
  updateMetaVar m $ \mv -> mv { mvListeners = Set.insert l $ mvListeners mv }

-- | Unregister a listener.
unlistenToMeta :: MonadMetaSolver m => Listener -> MetaId -> m ()
unlistenToMeta l m =
  updateMetaVar m $ \mv -> mv { mvListeners = Set.delete l $ mvListeners mv }

-- | Get the listeners for a local meta-variable.
getMetaListeners ::
  (HasCallStack, MonadDebug m, ReadTCState m) => MetaId -> m [Listener]
getMetaListeners m = Set.toList . mvListeners <$> lookupLocalMeta m

clearMetaListeners :: MonadMetaSolver m => MetaId -> m ()
clearMetaListeners m =
  updateMetaVar m $ \mv -> mv { mvListeners = Set.empty }

-- | Do safe eta-expansions for meta (@SingletonRecords,Levels@).
etaExpandMetaSafe :: (MonadMetaSolver m) => MetaId -> m ()
etaExpandMetaSafe = etaExpandMeta [SingletonRecords,Levels]

-- | Eta expand metavariables listening on the current meta.
etaExpandListeners :: MonadMetaSolver m => MetaId -> m ()
etaExpandListeners m = do
  ls <- getMetaListeners m
  clearMetaListeners m  -- we don't really have to do this
  mapM_ wakeupListener ls

-- | Wake up a meta listener and let it do its thing
wakeupListener :: MonadMetaSolver m => Listener -> m ()
  -- Andreas 2010-10-15: do not expand record mvars, lazyness needed for irrelevance
wakeupListener (EtaExpand x)         = etaExpandMetaSafe x
wakeupListener (CheckConstraint _ c) = do
  --reportSDoc "tc.meta.blocked" 20 $ "waking boxed constraint" <+> prettyTCM c
  modifyAwakeConstraints (c:)
  solveAwakeConstraints

solveAwakeConstraints :: (MonadConstraint m) => m ()
solveAwakeConstraints = solveAwakeConstraints' False

solveAwakeConstraints' :: (MonadConstraint m) => Bool -> m ()
solveAwakeConstraints' = solveSomeAwakeConstraints (const True)

---------------------------------------------------------------------------
-- * Freezing and unfreezing metas.
---------------------------------------------------------------------------

{-# SPECIALIZE freezeMetas :: LocalMetaStore -> TCM (Set MetaId) #-}
-- | Freeze the given meta-variables (but only if they are open) and
-- return those that were not already frozen.
freezeMetas :: forall m. MonadTCState m => LocalMetaStore -> m (Set MetaId)
freezeMetas ms =
  execWriterT $
  modifyTCLensM stOpenMetaStore $
  execStateT (mapM_ freeze $ MapS.keys ms)
  where
  freeze :: MetaId -> StateT LocalMetaStore (WriterT (Set MetaId) m) ()
  freeze m = do
    store <- get
    case MapS.lookup m store of
      Just mvar
        | mvFrozen mvar /= Frozen -> do
          lift $ tell (Set.singleton m)
          put $ MapS.insert m (mvar { mvFrozen = Frozen }) store
        | otherwise -> return ()
      Nothing -> return ()

-- | Thaw all open meta variables.
unfreezeMetas :: TCM ()
unfreezeMetas = stOpenMetaStore `modifyTCLens` MapS.map unfreeze
  where
  unfreeze :: MetaVariable -> MetaVariable
  unfreeze mvar = mvar { mvFrozen = Instantiable }

{-# SPECIALIZE isFrozen :: MetaId -> TCM Bool #-}
isFrozen ::
  (HasCallStack, MonadDebug m, ReadTCState m) => MetaId -> m Bool
isFrozen x = do
  mvar <- lookupLocalMeta x
  return $ mvFrozen mvar == Frozen

withFrozenMetas ::
    (MonadMetaSolver m, MonadTCState m)
  => m a -> m a
withFrozenMetas act = do
  openMetas <- useR stOpenMetaStore
  frozenMetas <- freezeMetas openMetas
  result <- act
  forM_ frozenMetas $ \m ->
    updateMetaVar m $ \ mv -> mv { mvFrozen = Instantiable }
  return result

-- | Unfreeze a meta and its type if this is a meta again.
--   Does not unfreeze deep occurrences of meta-variables or remote
--   meta-variables.
class UnFreezeMeta a where
  unfreezeMeta :: MonadMetaSolver m => a -> m ()

instance UnFreezeMeta MetaId where
  unfreezeMeta x = unlessM (($ x) <$> isRemoteMeta) $ do
    updateMetaVar x $ \ mv -> mv { mvFrozen = Instantiable }
    unfreezeMeta =<< metaType x
{-# SPECIALIZE unfreezeMeta :: MetaId -> TCM () #-}

instance UnFreezeMeta Type where
  unfreezeMeta (El s t) = unfreezeMeta s >> unfreezeMeta t

instance UnFreezeMeta Term where
  unfreezeMeta (MetaV x _)   = unfreezeMeta x
  unfreezeMeta (Sort s)      = unfreezeMeta s
  unfreezeMeta (Level l)     = unfreezeMeta l
  unfreezeMeta (DontCare t)  = unfreezeMeta t
  unfreezeMeta (Lam _ v)     = unfreezeMeta v
  unfreezeMeta _             = return ()

instance UnFreezeMeta Sort where
  unfreezeMeta (MetaS x _)   = unfreezeMeta x
  unfreezeMeta _             = return ()

instance UnFreezeMeta Level where
  unfreezeMeta (Max _ ls)      = unfreezeMeta ls

instance UnFreezeMeta PlusLevel where
  unfreezeMeta (Plus _ a)    = unfreezeMeta a

instance UnFreezeMeta a => UnFreezeMeta [a] where
  unfreezeMeta = mapM_ unfreezeMeta

instance UnFreezeMeta a => UnFreezeMeta (Abs a) where
  unfreezeMeta = Fold.mapM_ unfreezeMeta

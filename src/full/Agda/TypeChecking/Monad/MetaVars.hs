{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Monad.MetaVars where

import Prelude hiding (null)

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Fail (MonadFail)

import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Foldable as Fold

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin (HasBuiltins)
import Agda.TypeChecking.Monad.Trace
import Agda.TypeChecking.Monad.Closure
import Agda.TypeChecking.Monad.Constraints (MonadConstraint)
import Agda.TypeChecking.Monad.Debug (MonadDebug, reportSLn)
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Signature (HasConstInfo)
import Agda.TypeChecking.Substitute
import {-# SOURCE #-} Agda.TypeChecking.Telescope

import Agda.Utils.Except
import Agda.Utils.Functor ((<.>))
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Pretty (prettyShow)
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

  -- | Eta expand a metavariable, if it is of the specified kind.
  --   Don't do anything if the metavariable is a blocked term.
  etaExpandMeta :: [MetaKind] -> MetaId -> m ()

  -- | Update the status of the metavariable
  updateMetaVar :: MetaId -> (MetaVariable -> MetaVariable) -> m ()

  -- | 'speculateMetas fallback m' speculatively runs 'm', but if the
  --    result is 'RollBackMetas' any changes to metavariables are
  --    rolled back and 'fallback' is run instead.
  speculateMetas :: m () -> m KeepMetas -> m ()

-- | Switch off assignment of metas.
dontAssignMetas :: (MonadTCEnv m, HasOptions m, MonadDebug m) => m a -> m a
dontAssignMetas cont = do
  reportSLn "tc.meta" 45 $ "don't assign metas"
  localTC (\ env -> env { envAssignMetas = False }) cont

-- | Get the meta store.
getMetaStore :: (ReadTCState m) => m MetaStore
getMetaStore = useR stMetaStore

modifyMetaStore :: (MetaStore -> MetaStore) -> TCM ()
modifyMetaStore f = stMetaStore `modifyTCLens` f

-- | Run a computation and record which new metas it created.
metasCreatedBy :: ReadTCState m => m a -> m (a, IntSet)
metasCreatedBy m = do
  before <- IntMap.keysSet <$> useTC stMetaStore
  a <- m
  after  <- IntMap.keysSet <$> useTC stMetaStore
  return (a, after IntSet.\\ before)

-- | Lookup a meta variable.
lookupMeta' :: ReadTCState m => MetaId -> m (Maybe MetaVariable)
lookupMeta' m = IntMap.lookup (metaId m) <$> getMetaStore

lookupMeta :: (MonadFail m, ReadTCState m) => MetaId -> m MetaVariable
lookupMeta m = fromMaybeM failure $ lookupMeta' m
  where failure = fail $ "no such meta variable " ++ prettyShow m

-- | Type of a term or sort meta.
metaType :: (MonadFail m, ReadTCState m) => MetaId -> m Type
metaType x = jMetaType . mvJudgement <$> lookupMeta x

-- | Update the information associated with a meta variable.
updateMetaVarTCM :: MetaId -> (MetaVariable -> MetaVariable) -> TCM ()
updateMetaVarTCM m f = modifyMetaStore $ IntMap.adjust f $ metaId m

-- | Insert a new meta variable with associated information into the meta store.
insertMetaVar :: MetaId -> MetaVariable -> TCM ()
insertMetaVar m mv = modifyMetaStore $ IntMap.insert (metaId m) mv

getMetaPriority :: (MonadFail m, ReadTCState m) => MetaId -> m MetaPriority
getMetaPriority = mvPriority <.> lookupMeta

isSortMeta :: (MonadFail m, ReadTCState m) => MetaId -> m Bool
isSortMeta m = isSortMeta_ <$> lookupMeta m

isSortMeta_ :: MetaVariable -> Bool
isSortMeta_ mv = case mvJudgement mv of
    HasType{} -> False
    IsSort{}  -> True

getMetaType :: (MonadFail m, ReadTCState m) => MetaId -> m Type
getMetaType m = do
  mv <- lookupMeta m
  return $ case mvJudgement mv of
    HasType{ jMetaType = t } -> t
    IsSort{}  -> __IMPOSSIBLE__

-- | Compute the context variables that a meta should be applied to, accounting
--   for pruning.
getMetaContextArgs :: MonadTCEnv m => MetaVariable -> m Args
getMetaContextArgs MetaVar{ mvPermutation = p } = do
  args <- getContextArgs
  return $ permute (takeP (length args) p) args

-- | Given a meta, return the type applied to the current context.
getMetaTypeInContext :: (MonadFail m, MonadTCEnv m, ReadTCState m, MonadReduce m)
                     => MetaId -> m Type
getMetaTypeInContext m = do
  mv@MetaVar{ mvJudgement = j } <- lookupMeta m
  case j of
    HasType{ jMetaType = t } -> piApplyM t =<< getMetaContextArgs mv
    IsSort{}                 -> __IMPOSSIBLE__

-- | Is it a meta that might be generalized?
isGeneralizableMeta :: (ReadTCState m, MonadFail m) => MetaId -> m DoGeneralize
isGeneralizableMeta x = unArg . miGeneralizable . mvInfo <$> lookupMeta x

-- | Check whether all metas are instantiated.
--   Precondition: argument is a meta (in some form) or a list of metas.
class IsInstantiatedMeta a where
  isInstantiatedMeta :: (MonadFail m, ReadTCState m) => a -> m Bool

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

instance IsInstantiatedMeta LevelAtom where
  isInstantiatedMeta (MetaLevel x es) = isInstantiatedMeta x
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

isInstantiatedMeta' :: (MonadFail m, ReadTCState m) => MetaId -> m (Maybe Term)
isInstantiatedMeta' m = do
  mv <- lookupMeta m
  return $ case mvInstantiation mv of
    InstV tel v -> Just $ foldr mkLam v tel
    _           -> Nothing


-- | Returns all metavariables in a constraint. Slightly complicated by the
--   fact that blocked terms are represented by two meta variables. To find the
--   second one we need to look up the meta listeners for the one in the
--   UnBlock constraint.
constraintMetas :: Constraint -> TCM (Set MetaId)
constraintMetas c = metas c
  where
    -- We don't use allMetas here since some constraints should not stop us from generalizing. For
    -- instance CheckSizeLtSat (see #3694). We also have to check meta listeners to get metas of
    -- UnBlock constraints.
    metas c = case c of
      ValueCmp _ t u v         -> return $ allMetas Set.singleton (t, u, v)
      ValueCmpOnFace _ p t u v -> return $ allMetas Set.singleton (p, t, u, v)
      ElimCmp _ _ t u es es'   -> return $ allMetas Set.singleton (t, u, es, es')
      LevelCmp _ l l'          -> return $ allMetas Set.singleton (Level l, Level l')
      UnquoteTactic m t h g    -> return $ Set.fromList [x | Just x <- [m]] `Set.union` allMetas Set.singleton (t, h, g)
      Guarded c _              -> metas c
      TelCmp _ _ _ tel1 tel2   -> return $ allMetas Set.singleton (tel1, tel2)
      SortCmp _ s1 s2          -> return $ allMetas Set.singleton (Sort s1, Sort s2)
      UnBlock x                -> Set.insert x . Set.unions <$> (mapM listenerMetas =<< getMetaListeners x)
      FindInstance{}           -> return mempty  -- v Ignore these constraints
      IsEmpty{}                -> return mempty
      CheckFunDef{}            -> return mempty
      CheckSizeLtSat{}         -> return mempty
      HasBiggerSort{}          -> return mempty
      HasPTSRule{}             -> return mempty
      CheckMetaInst x          -> return mempty

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
  r   <- getCurrentRange
  cl  <- buildClosure r
  gen <- viewTC eGeneralizeMetas
  return MetaInfo
    { miClosRange       = cl
    , miMetaOccursCheck = b
    , miNameSuggestion  = ""
    , miGeneralizable   = hide $ defaultArg gen
    }

setValueMetaName :: MonadMetaSolver m => Term -> MetaNameSuggestion -> m ()
setValueMetaName v s = do
  case v of
    MetaV mi _ -> setMetaNameSuggestion mi s
    u          -> do
      reportSLn "tc.meta.name" 70 $
        "cannot set meta name; newMeta returns " ++ show u
      return ()

getMetaNameSuggestion :: (MonadFail m, ReadTCState m) => MetaId -> m MetaNameSuggestion
getMetaNameSuggestion mi = miNameSuggestion . mvInfo <$> lookupMeta mi

setMetaNameSuggestion :: MonadMetaSolver m => MetaId -> MetaNameSuggestion -> m ()
setMetaNameSuggestion mi s = unless (null s || isUnderscore s) $ do
  reportSLn "tc.meta.name" 20 $
    "setting name of meta " ++ prettyShow mi ++ " to " ++ s
  updateMetaVar mi $ \ mvar ->
    mvar { mvInfo = (mvInfo mvar) { miNameSuggestion = s }}

setMetaArgInfo :: MonadMetaSolver m => MetaId -> ArgInfo -> m ()
setMetaArgInfo m i = updateMetaVar m $ \ mv ->
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
  modifyInteractionPoints :: (InteractionPoints -> InteractionPoints) -> m ()

instance MonadInteractionPoints m => MonadInteractionPoints (ReaderT r m) where
  freshInteractionId = lift freshInteractionId
  modifyInteractionPoints = lift . modifyInteractionPoints

instance MonadInteractionPoints m => MonadInteractionPoints (StateT r m) where
  freshInteractionId = lift freshInteractionId
  modifyInteractionPoints = lift . modifyInteractionPoints

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
  let ip = InteractionPoint { ipRange = r, ipMeta = Nothing, ipSolved = False, ipClause = IPNoClause }
  case Map.insertLookupWithKey (\ key new old -> old) ii ip m of
    -- If the interaction point is already present, we keep the old ip.
    -- However, it needs to be at the same range as the new one.
    (Just ip0, _)
       | ipRange ip /= ipRange ip0 -> __IMPOSSIBLE__
       | otherwise                 -> return ii
    (Nothing, m') -> do
      modifyInteractionPoints (const m')
      return ii

-- | Find an interaction point by 'Range' by searching the whole map.
--
--   O(n): linear in the number of registered interaction points.

findInteractionPoint_ :: Range -> InteractionPoints -> Maybe InteractionId
findInteractionPoint_ r m = do
  guard $ not $ null r
  listToMaybe $ mapMaybe sameRange $ Map.toList m
  where
    sameRange :: (InteractionId, InteractionPoint) -> Maybe InteractionId
    sameRange (ii, InteractionPoint r' _ _ _) | r == r' = Just ii
    sameRange _ = Nothing

-- | Hook up meta variable to interaction point.
connectInteractionPoint
  :: MonadInteractionPoints m
  => InteractionId -> MetaId -> m ()
connectInteractionPoint ii mi = do
  ipCl <- asksTC envClause
  m <- useR stInteractionPoints
  let ip = InteractionPoint { ipRange = __IMPOSSIBLE__, ipMeta = Just mi, ipSolved = False, ipClause = ipCl }
  -- The interaction point needs to be present already, we just set the meta.
  case Map.insertLookupWithKey (\ key new old -> new { ipRange = ipRange old }) ii ip m of
    (Nothing, _) -> __IMPOSSIBLE__
    (Just _, m') -> modifyInteractionPoints $ const m'

-- | Mark an interaction point as solved.
removeInteractionPoint :: MonadInteractionPoints m => InteractionId -> m ()
removeInteractionPoint ii =
  modifyInteractionPoints $ Map.update (\ ip -> Just ip{ ipSolved = True }) ii

-- | Get a list of interaction ids.
{-# SPECIALIZE getInteractionPoints :: TCM [InteractionId] #-}
getInteractionPoints :: ReadTCState m => m [InteractionId]
getInteractionPoints = Map.keys <$> useR stInteractionPoints

-- | Get all metas that correspond to unsolved interaction ids.
getInteractionMetas :: ReadTCState m => m [MetaId]
getInteractionMetas =
  mapMaybe ipMeta . filter (not . ipSolved) . Map.elems <$> useR stInteractionPoints

-- | Get all metas that correspond to unsolved interaction ids.
getInteractionIdsAndMetas :: ReadTCState m => m [(InteractionId,MetaId)]
getInteractionIdsAndMetas =
  mapMaybe f . filter (not . ipSolved . snd) . Map.toList <$> useR stInteractionPoints
  where f (ii, ip) = (ii,) <$> ipMeta ip

-- | Does the meta variable correspond to an interaction point?
--
--   Time: @O(n)@ where @n@ is the number of interaction metas.
isInteractionMeta :: ReadTCState m => MetaId -> m (Maybe InteractionId)
isInteractionMeta x = lookup x . map swap <$> getInteractionIdsAndMetas

-- | Get the information associated to an interaction point.
{-# SPECIALIZE lookupInteractionPoint :: InteractionId -> TCM InteractionPoint #-}
lookupInteractionPoint
  :: (MonadFail m, ReadTCState m, MonadError TCErr m)
  => InteractionId -> m InteractionPoint
lookupInteractionPoint ii =
  fromMaybeM err $ Map.lookup ii <$> useR stInteractionPoints
  where
    err  = fail $ "no such interaction point: " ++ show ii

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
lookupInteractionMeta_ ii m = ipMeta =<< Map.lookup ii m

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

-- | Get the 'Range' for a meta variable.
getMetaRange :: (MonadFail m, ReadTCState m) => MetaId -> m Range
getMetaRange = getRange <.> lookupMeta

getInteractionScope :: InteractionId -> TCM ScopeInfo
getInteractionScope = getMetaScope <.> lookupMeta <=< lookupInteractionId

withMetaInfo' :: MetaVariable -> TCM a -> TCM a
withMetaInfo' mv = withMetaInfo (miClosRange $ mvInfo mv)

withMetaInfo :: Closure Range -> TCM a -> TCM a
withMetaInfo mI cont = enterClosure mI $ \ r ->
  setCurrentRange r cont

getMetaVariableSet :: ReadTCState m => m IntSet
getMetaVariableSet = IntMap.keysSet <$> getMetaStore

getMetaVariables :: ReadTCState m => (MetaVariable -> Bool) -> m [MetaId]
getMetaVariables p = do
  store <- getMetaStore
  return [ MetaId i | (i, mv) <- IntMap.assocs store, p mv ]

getInstantiatedMetas :: ReadTCState m => m [MetaId]
getInstantiatedMetas = getMetaVariables (isInst . mvInstantiation)
  where
    isInst Open                           = False
    isInst OpenInstance                   = False
    isInst BlockedConst{}                 = False
    isInst PostponedTypeCheckingProblem{} = False
    isInst InstV{}                        = True

getOpenMetas :: ReadTCState m => m [MetaId]
getOpenMetas = getMetaVariables (isOpenMeta . mvInstantiation)

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

-- | Get the listeners to a meta.
getMetaListeners :: (MonadFail m, ReadTCState m) => MetaId -> m [Listener]
getMetaListeners m = Set.toList . mvListeners <$> lookupMeta m

clearMetaListeners :: MonadMetaSolver m => MetaId -> m ()
clearMetaListeners m =
  updateMetaVar m $ \mv -> mv { mvListeners = Set.empty }

---------------------------------------------------------------------------
-- * Freezing and unfreezing metas.
---------------------------------------------------------------------------

-- | Freeze all so far unfrozen metas for the duration of the given computation.
withFreezeMetas :: TCM a -> TCM a
withFreezeMetas cont = do
  ms <- Set.fromList <$> freezeMetas
  x  <- cont
  unfreezeMetas' (`Set.member` ms)
  return x

-- | Freeze all meta variables and return the list of metas that got frozen.
freezeMetas :: TCM [MetaId]
freezeMetas = freezeMetas' $ const True

-- | Freeze some meta variables and return the list of metas that got frozen.
freezeMetas' :: (MetaId -> Bool) -> TCM [MetaId]
freezeMetas' p = execWriterT $ modifyTCLensM stMetaStore $ IntMap.traverseWithKey (freeze . MetaId)
  where
  freeze :: Monad m => MetaId -> MetaVariable -> WriterT [MetaId] m MetaVariable
  freeze m mvar
    | p m && mvFrozen mvar /= Frozen = do
        tell [m]
        return $ mvar { mvFrozen = Frozen }
    | otherwise = return mvar

-- | Thaw all meta variables.
unfreezeMetas :: TCM ()
unfreezeMetas = unfreezeMetas' $ const True

-- | Thaw some metas, as indicated by the passed condition.
unfreezeMetas' :: (MetaId -> Bool) -> TCM ()
unfreezeMetas' cond = modifyMetaStore $ IntMap.mapWithKey $ unfreeze . MetaId
  where
  unfreeze :: MetaId -> MetaVariable -> MetaVariable
  unfreeze m mvar
    | cond m    = mvar { mvFrozen = Instantiable }
    | otherwise = mvar

isFrozen :: (MonadFail m, ReadTCState m) => MetaId -> m Bool
isFrozen x = do
  mvar <- lookupMeta x
  return $ mvFrozen mvar == Frozen

-- | Unfreeze meta and its type if this is a meta again.
--   Does not unfreeze deep occurrences of metas.
class UnFreezeMeta a where
  unfreezeMeta :: MonadMetaSolver m => a -> m ()

instance UnFreezeMeta MetaId where
  unfreezeMeta x = do
    updateMetaVar x $ \ mv -> mv { mvFrozen = Instantiable }
    unfreezeMeta =<< metaType x

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

instance UnFreezeMeta LevelAtom where
  unfreezeMeta (MetaLevel x _)    = unfreezeMeta x
  unfreezeMeta (BlockedLevel _ t) = unfreezeMeta t
  unfreezeMeta (NeutralLevel _ t) = unfreezeMeta t
  unfreezeMeta (UnreducedLevel t) = unfreezeMeta t

instance UnFreezeMeta a => UnFreezeMeta [a] where
  unfreezeMeta = mapM_ unfreezeMeta

instance UnFreezeMeta a => UnFreezeMeta (Abs a) where
  unfreezeMeta = Fold.mapM_ unfreezeMeta

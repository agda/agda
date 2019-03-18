{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Monad.MetaVars where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Foldable as Fold

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Trace
import Agda.TypeChecking.Monad.Closure
import Agda.TypeChecking.Monad.Debug (reportSLn)
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Substitute
import {-# SOURCE #-} Agda.TypeChecking.Telescope

import Agda.Utils.Functor ((<.>))
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Tuple
import Agda.Utils.Size
import qualified Agda.Utils.Maybe.Strict as Strict

#include "undefined.h"
import Agda.Utils.Impossible

-- | Switch off assignment of metas.
dontAssignMetas :: TCM a -> TCM a
dontAssignMetas cont = do
  reportSLn "tc.meta" 45 $ "don't assign metas"
  localTC (\ env -> env { envAssignMetas = False }) cont

-- | Get the meta store.
getMetaStore :: TCM MetaStore
getMetaStore = useTC stMetaStore

modifyMetaStore :: (MetaStore -> MetaStore) -> TCM ()
modifyMetaStore f = stMetaStore `modifyTCLens` f

-- | Run a computation and record which new metas it created.
metasCreatedBy :: TCM a -> TCM (a, IntSet)
metasCreatedBy m = do
  before <- IntMap.keysSet <$> useTC stMetaStore
  a <- m
  after  <- IntMap.keysSet <$> useTC stMetaStore
  return (a, after IntSet.\\ before)

-- | Lookup a meta variable.
lookupMeta' :: MetaId -> TCM (Maybe MetaVariable)
lookupMeta' m = IntMap.lookup (metaId m) <$> getMetaStore

lookupMeta :: MetaId -> TCM MetaVariable
lookupMeta m = fromMaybeM failure $ lookupMeta' m
  where failure = fail $ "no such meta variable " ++ prettyShow m

-- | Update the information associated with a meta variable.
updateMetaVar :: MetaId -> (MetaVariable -> MetaVariable) -> TCM ()
updateMetaVar m f = modifyMetaStore $ IntMap.adjust f $ metaId m

-- | Insert a new meta variable with associated information into the meta store.
insertMetaVar :: MetaId -> MetaVariable -> TCM ()
insertMetaVar m mv = modifyMetaStore $ IntMap.insert (metaId m) mv

getMetaPriority :: MetaId -> TCM MetaPriority
getMetaPriority = mvPriority <.> lookupMeta

isSortMeta :: MetaId -> TCM Bool
isSortMeta m = isSortMeta_ <$> lookupMeta m

isSortMeta_ :: MetaVariable -> Bool
isSortMeta_ mv = case mvJudgement mv of
    HasType{} -> False
    IsSort{}  -> True

getMetaType :: MetaId -> TCM Type
getMetaType m = do
  mv <- lookupMeta m
  return $ case mvJudgement mv of
    HasType{ jMetaType = t } -> t
    IsSort{}  -> __IMPOSSIBLE__

-- | Compute the context variables that a meta should be applied to, accounting
--   for pruning.
getMetaContextArgs :: MetaVariable -> TCM Args
getMetaContextArgs MetaVar{ mvPermutation = p } = do
  args <- getContextArgs
  return $ permute (takeP (length args) p) args

-- | Given a meta, return the type applied to the current context.
getMetaTypeInContext :: MetaId -> TCM Type
getMetaTypeInContext m = do
  mv@MetaVar{ mvJudgement = j } <- lookupMeta m
  case j of
    HasType{ jMetaType = t } -> piApplyM t =<< getMetaContextArgs mv
    IsSort{}                 -> __IMPOSSIBLE__

-- | Check whether all metas are instantiated.
--   Precondition: argument is a meta (in some form) or a list of metas.
class IsInstantiatedMeta a where
  isInstantiatedMeta :: a -> TCM Bool

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
  isInstantiatedMeta (Max ls) = isInstantiatedMeta ls

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

isInstantiatedMeta' :: MetaId -> TCM (Maybe Term)
isInstantiatedMeta' m = do
  mv <- lookupMeta m
  return $ case mvInstantiation mv of
    InstV tel v -> Just $ foldr mkLam v tel
    _           -> Nothing


-- | Returns every meta-variable occurrence in the given type, except
-- for those in 'Sort's.
allMetas :: TermLike a => a -> [MetaId]
allMetas = foldTerm metas
  where
  metas (MetaV m _) = [m]
  metas (Level l)   = levelMetas l
  metas _           = []

  levelMetas (Max as) = concatMap plusLevelMetas as

  plusLevelMetas ClosedLevel{} = []
  plusLevelMetas (Plus _ l)    = levelAtomMetas l

  levelAtomMetas (MetaLevel m _) = [m]
  levelAtomMetas _               = []

-- | Create 'MetaInfo' in the current environment.
createMetaInfo :: TCM MetaInfo
createMetaInfo = createMetaInfo' RunMetaOccursCheck

createMetaInfo' :: RunMetaOccursCheck -> TCM MetaInfo
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

setValueMetaName :: Term -> MetaNameSuggestion -> TCM ()
setValueMetaName v s = do
  case v of
    MetaV mi _ -> setMetaNameSuggestion mi s
    u          -> do
      reportSLn "tc.meta.name" 70 $
        "cannot set meta name; newMeta returns " ++ show u
      return ()

getMetaNameSuggestion :: MetaId -> TCM MetaNameSuggestion
getMetaNameSuggestion mi = miNameSuggestion . mvInfo <$> lookupMeta mi

setMetaNameSuggestion :: MetaId -> MetaNameSuggestion -> TCM ()
setMetaNameSuggestion mi s = unless (null s || isUnderscore s) $ do
  reportSLn "tc.meta.name" 20 $
    "setting name of meta " ++ prettyShow mi ++ " to " ++ s
  updateMetaVar mi $ \ mvar ->
    mvar { mvInfo = (mvInfo mvar) { miNameSuggestion = s }}

setMetaArgInfo :: MetaId -> ArgInfo -> TCM ()
setMetaArgInfo m i = updateMetaVar m $ \ mv ->
  mv { mvInfo = (mvInfo mv)
        { miGeneralizable = setArgInfo i (miGeneralizable (mvInfo mv)) } }

updateMetaVarRange :: MetaId -> Range -> TCM ()
updateMetaVarRange mi r = updateMetaVar mi (setRange r)

setMetaOccursCheck :: MetaId -> RunMetaOccursCheck -> TCM ()
setMetaOccursCheck mi b = updateMetaVar mi $ \ mvar ->
  mvar { mvInfo = (mvInfo mvar) { miMetaOccursCheck = b } }

-- * Query and manipulate interaction points.

modifyInteractionPoints :: (InteractionPoints -> InteractionPoints) -> TCM ()
modifyInteractionPoints f =
  stInteractionPoints `modifyTCLens` f

-- | Register an interaction point during scope checking.
--   If there is no interaction id yet, create one.
registerInteractionPoint :: Bool -> Range -> Maybe Nat -> TCM InteractionId
registerInteractionPoint preciseRange r maybeId = do
  m <- useTC stInteractionPoints
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
 continue m = do
  -- We did not find an interaction id with the same Range, so let's create one!
  ii <- case maybeId of
    Just i  -> return $ InteractionId i
    Nothing -> fresh
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
  headMaybe $ mapMaybe sameRange $ Map.toList m
  where
    sameRange :: (InteractionId, InteractionPoint) -> Maybe InteractionId
    sameRange (ii, InteractionPoint r' _ _ _) | r == r' = Just ii
    sameRange _ = Nothing

-- | Hook up meta variable to interaction point.
connectInteractionPoint :: InteractionId -> MetaId -> TCM ()
connectInteractionPoint ii mi = do
  ipCl <- asksTC envClause
  m <- useTC stInteractionPoints
  let ip = InteractionPoint { ipRange = __IMPOSSIBLE__, ipMeta = Just mi, ipSolved = False, ipClause = ipCl }
  -- The interaction point needs to be present already, we just set the meta.
  case Map.insertLookupWithKey (\ key new old -> new { ipRange = ipRange old }) ii ip m of
    (Nothing, _) -> __IMPOSSIBLE__
    (Just _, m') -> modifyInteractionPoints $ const m'

-- | Mark an interaction point as solved.
removeInteractionPoint :: InteractionId -> TCM ()
removeInteractionPoint ii = do
  stInteractionPoints `modifyTCLens` Map.update (\ ip -> Just ip{ ipSolved = True }) ii

-- | Get a list of interaction ids.
{-# SPECIALIZE getInteractionPoints :: TCM [InteractionId] #-}
getInteractionPoints :: MonadTCM tcm => tcm [InteractionId]
getInteractionPoints = Map.keys <$> useTC stInteractionPoints

-- | Get all metas that correspond to unsolved interaction ids.
getInteractionMetas :: TCM [MetaId]
getInteractionMetas =
  mapMaybe ipMeta . filter (not . ipSolved) . Map.elems <$> useTC stInteractionPoints

-- | Get all metas that correspond to unsolved interaction ids.
getInteractionIdsAndMetas :: TCM [(InteractionId,MetaId)]
getInteractionIdsAndMetas =
  mapMaybe f . filter (not . ipSolved . snd) . Map.toList <$> useTC stInteractionPoints
  where f (ii, ip) = (ii,) <$> ipMeta ip

-- | Does the meta variable correspond to an interaction point?
--
--   Time: @O(n)@ where @n@ is the number of interaction metas.
isInteractionMeta :: MetaId -> TCM (Maybe InteractionId)
isInteractionMeta x = lookup x . map swap <$> getInteractionIdsAndMetas

-- | Get the information associated to an interaction point.
{-# SPECIALIZE lookupInteractionPoint :: InteractionId -> TCM InteractionPoint #-}
lookupInteractionPoint :: MonadTCM tcm => InteractionId -> tcm InteractionPoint
lookupInteractionPoint ii =
  fromMaybeM err $ Map.lookup ii <$> useTC stInteractionPoints
  where
    err  = fail $ "no such interaction point: " ++ show ii

-- | Get 'MetaId' for an interaction point.
--   Precondition: interaction point is connected.
lookupInteractionId :: InteractionId -> TCM MetaId
lookupInteractionId ii = fromMaybeM err2 $ ipMeta <$> lookupInteractionPoint ii
  where
    err2 = typeError $ GenericError $ "No type nor action available for hole " ++ prettyShow ii ++ ". Possible cause: the hole has not been reached during type checking (do you see yellow?)"

-- | Check whether an interaction id is already associated with a meta variable.
lookupInteractionMeta :: InteractionId -> TCM (Maybe MetaId)
lookupInteractionMeta ii = lookupInteractionMeta_ ii <$> useTC stInteractionPoints

lookupInteractionMeta_ :: InteractionId -> InteractionPoints -> Maybe MetaId
lookupInteractionMeta_ ii m = ipMeta =<< Map.lookup ii m

-- | Generate new meta variable.
newMeta :: Frozen -> MetaInfo -> MetaPriority -> Permutation -> Judgement a -> TCM MetaId
newMeta = newMeta' Open

-- | Generate a new meta variable with some instantiation given.
--   For instance, the instantiation could be a 'PostponedTypeCheckingProblem'.
newMeta' :: MetaInstantiation -> Frozen -> MetaInfo -> MetaPriority -> Permutation ->
            Judgement a -> TCM MetaId
newMeta' inst frozen mi p perm j = do
  x <- fresh
  let j' = j { jMetaId = x }  -- fill the identifier part of the judgement
      mv = MetaVar{ mvInfo             = mi
                  , mvPriority         = p
                  , mvPermutation      = perm
                  , mvJudgement        = j'
                  , mvInstantiation    = inst
                  , mvListeners        = Set.empty
                  , mvFrozen           = frozen
                  }
  -- printing not available (import cycle)
  -- reportSDoc "tc.meta.new" 50 $ "new meta" <+> prettyTCM j'
  insertMetaVar x mv
  return x

-- | Get the 'Range' for an interaction point.
{-# SPECIALIZE getInteractionRange :: InteractionId -> TCM Range #-}
getInteractionRange :: MonadTCM tcm => InteractionId -> tcm Range
getInteractionRange = ipRange <.> lookupInteractionPoint

-- | Get the 'Range' for a meta variable.
getMetaRange :: MetaId -> TCM Range
getMetaRange = getRange <.> lookupMeta

getInteractionScope :: InteractionId -> TCM ScopeInfo
getInteractionScope = getMetaScope <.> lookupMeta <=< lookupInteractionId

withMetaInfo' :: MetaVariable -> TCM a -> TCM a
withMetaInfo' mv = withMetaInfo (miClosRange $ mvInfo mv)

withMetaInfo :: Closure Range -> TCM a -> TCM a
withMetaInfo mI cont = enterClosure mI $ \ r ->
  setCurrentRange r cont

getMetaVariableSet :: TCM IntSet
getMetaVariableSet = IntMap.keysSet <$> getMetaStore

getMetaVariables :: (MetaVariable -> Bool) -> TCM [MetaId]
getMetaVariables p = do
  store <- getMetaStore
  return [ MetaId i | (i, mv) <- IntMap.assocs store, p mv ]

getInstantiatedMetas :: TCM [MetaId]
getInstantiatedMetas = getMetaVariables (isInst . mvInstantiation)
  where
    isInst Open                           = False
    isInst OpenInstance                   = False
    isInst BlockedConst{}                 = False
    isInst PostponedTypeCheckingProblem{} = False
    isInst InstV{}                        = True

getOpenMetas :: TCM [MetaId]
getOpenMetas = getMetaVariables (isOpenMeta . mvInstantiation)

isOpenMeta :: MetaInstantiation -> Bool
isOpenMeta Open                           = True
isOpenMeta OpenInstance                   = True
isOpenMeta BlockedConst{}                 = True
isOpenMeta PostponedTypeCheckingProblem{} = True
isOpenMeta InstV{}                        = False

-- | @listenToMeta l m@: register @l@ as a listener to @m@. This is done
--   when the type of l is blocked by @m@.
listenToMeta :: Listener -> MetaId -> TCM ()
listenToMeta l m =
  updateMetaVar m $ \mv -> mv { mvListeners = Set.insert l $ mvListeners mv }

-- | Unregister a listener.
unlistenToMeta :: Listener -> MetaId -> TCM ()
unlistenToMeta l m =
  updateMetaVar m $ \mv -> mv { mvListeners = Set.delete l $ mvListeners mv }

-- | Get the listeners to a meta.
getMetaListeners :: MetaId -> TCM [Listener]
getMetaListeners m = Set.toList . mvListeners <$> lookupMeta m

clearMetaListeners :: MetaId -> TCM ()
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

isFrozen :: MetaId -> TCM Bool
isFrozen x = do
  mvar <- lookupMeta x
  return $ mvFrozen mvar == Frozen

-- | Unfreeze meta and its type if this is a meta again.
--   Does not unfreeze deep occurrences of metas.
class UnFreezeMeta a where
  unfreezeMeta :: a -> TCM ()

instance UnFreezeMeta MetaId where
  unfreezeMeta x = do
    updateMetaVar x $ \ mv -> mv { mvFrozen = Instantiable }
    unfreezeMeta =<< do jMetaType . mvJudgement <$> lookupMeta x

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
  unfreezeMeta (Max ls)      = unfreezeMeta ls

instance UnFreezeMeta PlusLevel where
  unfreezeMeta (Plus _ a)    = unfreezeMeta a
  unfreezeMeta ClosedLevel{} = return ()

instance UnFreezeMeta LevelAtom where
  unfreezeMeta (MetaLevel x _)    = unfreezeMeta x
  unfreezeMeta (BlockedLevel _ t) = unfreezeMeta t
  unfreezeMeta (NeutralLevel _ t) = unfreezeMeta t
  unfreezeMeta (UnreducedLevel t) = unfreezeMeta t

instance UnFreezeMeta a => UnFreezeMeta [a] where
  unfreezeMeta = mapM_ unfreezeMeta

instance UnFreezeMeta a => UnFreezeMeta (Abs a) where
  unfreezeMeta = Fold.mapM_ unfreezeMeta

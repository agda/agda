{-# OPTIONS_GHC -fwarn-missing-signatures #-}

{-# LANGUAGE CPP                  #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Agda.TypeChecking.Monad.MetaVars where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Foldable as Fold
import qualified Data.Traversable as Trav

import Agda.Syntax.Common as Common
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Trace
import Agda.TypeChecking.Monad.Closure
import Agda.TypeChecking.Monad.Options (reportSLn)
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Substitute

import Agda.Utils.Functor ((<.>))
import Agda.Utils.Fresh
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Tuple
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

-- | Switch off assignment of metas.
dontAssignMetas :: TCM a -> TCM a
dontAssignMetas = local $ \ env -> env { envAssignMetas = False }

-- | Get the meta store.
getMetaStore :: TCM MetaStore
getMetaStore = gets stMetaStore

modifyMetaStore :: (MetaStore -> MetaStore) -> TCM ()
modifyMetaStore f = modify $ \ st -> st { stMetaStore = f (stMetaStore st) }

-- | Lookup a meta variable
lookupMeta :: MetaId -> TCM MetaVariable
lookupMeta m = fromMaybeM failure $ Map.lookup m <$> getMetaStore
  where failure = fail $ "no such meta variable " ++ show m

updateMetaVar :: MetaId -> (MetaVariable -> MetaVariable) -> TCM ()
updateMetaVar m f = modifyMetaStore $ Map.adjust f m

getMetaPriority :: MetaId -> TCM MetaPriority
getMetaPriority = mvPriority <.> lookupMeta

{- UNUSED
getMetaRelevance :: MetaId -> TCM Relevance
getMetaRelevance x = miRelevance . mvInfo <$> lookupMeta x
-}

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

-- | Given a meta, return the type applied to the current context.
getMetaTypeInContext :: MetaId -> TCM Type
getMetaTypeInContext m = do
  MetaVar{ mvJudgement = j, mvPermutation = p } <- lookupMeta m
  case j of
    HasType{ jMetaType = t } -> do
      vs <- getContextArgs
      return $ piApply t $ permute (takeP (size vs) p) vs
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
    case ignoreSharing v of
      MetaV x _  -> isInstantiatedMeta x
      DontCare v -> loop v
      Level l    -> isInstantiatedMeta l
      Lam _ b    -> isInstantiatedMeta b
      Con _ vs   -> isInstantiatedMeta vs
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

instance IsInstantiatedMeta a => IsInstantiatedMeta (Common.Arg c a) where
  isInstantiatedMeta = isInstantiatedMeta . unArg

-- | Does not worry about raising.
instance IsInstantiatedMeta a => IsInstantiatedMeta (Abs a) where
  isInstantiatedMeta = isInstantiatedMeta . unAbs

isInstantiatedMeta' :: MetaId -> TCM (Maybe Term)
isInstantiatedMeta' m = do
  mv <- lookupMeta m
  return $ case mvInstantiation mv of
    InstV v -> Just v
    InstS v -> Just v
    _       -> Nothing

-- | Create 'MetaInfo' in the current environment.
createMetaInfo :: TCM MetaInfo
createMetaInfo = createMetaInfo' RunMetaOccursCheck

createMetaInfo' :: RunMetaOccursCheck -> TCM MetaInfo
createMetaInfo' b = do
  r   <- getCurrentRange
  cl  <- buildClosure r
  return MetaInfo
    { miClosRange       = cl
    , miMetaOccursCheck = b
    , miNameSuggestion  = ""
    }

setValueMetaName :: Term -> MetaNameSuggestion -> TCM ()
setValueMetaName v s = do
  case ignoreSharing v of
    MetaV mi _ -> setMetaNameSuggestion mi s
    u          -> do
      reportSLn "tc.meta.name" 70 $
        "cannot set meta name; newMeta returns " ++ show u
      return ()

getMetaNameSuggestion :: MetaId -> TCM MetaNameSuggestion
getMetaNameSuggestion mi = miNameSuggestion . mvInfo <$> lookupMeta mi

setMetaNameSuggestion :: MetaId -> MetaNameSuggestion -> TCM ()
setMetaNameSuggestion mi s = do
  reportSLn "tc.meta.name" 20 $
    "setting name of meta " ++ show mi ++ " to " ++ s
  updateMetaVar mi $ \ mvar ->
    mvar { mvInfo = (mvInfo mvar) { miNameSuggestion = s }}

updateMetaVarRange :: MetaId -> Range -> TCM ()
updateMetaVarRange mi r = updateMetaVar mi (setRange r)

-- * Query and manipulate interaction points.

modifyInteractionPoints :: (InteractionPoints -> InteractionPoints) -> TCM ()
modifyInteractionPoints f =
  modify $ \ s -> s { stInteractionPoints = f (stInteractionPoints s) }

-- | Register an interaction point during scope checking.
--   If there is no interaction id yet, create one.
registerInteractionPoint :: Range -> Maybe Nat -> TCM InteractionId
registerInteractionPoint r maybeId = do
  ii <- case maybeId of
    Just i  -> return $ InteractionId i
    Nothing -> fresh
  m <- gets stInteractionPoints
  let ip = InteractionPoint { ipRange = r, ipMeta = Nothing }
  case Map.insertLookupWithKey (\ key new old -> old) ii ip m of
    -- If the interaction point is already present, we keep the old ip.
    -- However, it needs to be at the same range as the new one.
    (Just ip0, _)
       | ipRange ip /= ipRange ip0 -> __IMPOSSIBLE__
       | otherwise                 -> return ii
    (Nothing, m') -> do
      modifyInteractionPoints (const m')
      return ii

-- | Hook up meta variable to interaction point.
connectInteractionPoint :: InteractionId -> MetaId -> TCM ()
connectInteractionPoint ii mi = do
  m <- gets stInteractionPoints
  let ip = InteractionPoint { ipRange = __IMPOSSIBLE__, ipMeta = Just mi }
  -- The interaction point needs to be present already, we just set the meta.
  case Map.insertLookupWithKey (\ key new old -> new { ipRange = ipRange old }) ii ip m of
    (Nothing, _) -> __IMPOSSIBLE__
    (Just _, m') -> modifyInteractionPoints $ const m'

-- | Move an interaction point from the current ones to the old ones.
removeInteractionPoint :: InteractionId -> TCM ()
removeInteractionPoint ii = do
  scope <- getInteractionScope ii
  modifyInteractionPoints $ Map.delete ii

-- | Get a list of interaction ids.
getInteractionPoints :: TCM [InteractionId]
getInteractionPoints = Map.keys <$> gets stInteractionPoints

-- | Get all metas that correspond to interaction ids.
getInteractionMetas :: TCM [MetaId]
getInteractionMetas = mapMaybe ipMeta . Map.elems <$> gets stInteractionPoints

-- | Get all metas that correspond to interaction ids.
getInteractionIdsAndMetas :: TCM [(InteractionId,MetaId)]
getInteractionIdsAndMetas = mapMaybe f . Map.toList <$> gets stInteractionPoints
  where f (ii, ip) = (ii,) <$> ipMeta ip

-- | Does the meta variable correspond to an interaction point?
--
--   Time: @O(n)@ where @n@ is the number of interaction metas.
isInteractionMeta :: MetaId -> TCM (Maybe InteractionId)
isInteractionMeta x = lookup x . map swap <$> getInteractionIdsAndMetas

-- | Get the information associated to an interaction point.
lookupInteractionPoint :: InteractionId -> TCM InteractionPoint
lookupInteractionPoint ii =
  fromMaybeM err $ Map.lookup ii <$> gets stInteractionPoints
  where
    err  = fail $ "no such interaction point: " ++ show ii

-- | Get 'MetaId' for an interaction point.
--   Precondition: interaction point is connected.
lookupInteractionId :: InteractionId -> TCM MetaId
lookupInteractionId ii = fromMaybeM err2 $ ipMeta <$> lookupInteractionPoint ii
  where
    err2 = typeError $ GenericError $ "No type nor action available for hole " ++ show ii

-- | Generate new meta variable.
newMeta :: MetaInfo -> MetaPriority -> Permutation -> Judgement Type a -> TCM MetaId
newMeta = newMeta' Open

-- | Generate a new meta variable with some instantiation given.
--   For instance, the instantiation could be a 'PostponedTypeCheckingProblem'.
newMeta' :: MetaInstantiation -> MetaInfo -> MetaPriority -> Permutation ->
            Judgement Type a -> TCM MetaId
newMeta' inst mi p perm j = do
  x <- fresh
  let j' = fmap (const x) j  -- fill the identifier part of the judgement
      mv = MetaVar mi p perm j' inst Set.empty Instantiable
  -- printing not available (import cycle)
  -- reportSDoc "tc.meta.new" 50 $ text "new meta" <+> prettyTCM j'
  modify $ \st -> st { stMetaStore = Map.insert x mv $ stMetaStore st }
  return x

-- | Get the 'Range' for an interaction point.
getInteractionRange :: InteractionId -> TCM Range
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

getInstantiatedMetas :: TCM [MetaId]
getInstantiatedMetas = do
    store <- getMetaStore
    return [ i | (i, MetaVar{ mvInstantiation = mi }) <- Map.assocs store, isInst mi ]
    where
        isInst Open                               = False
        isInst OpenIFS                            = False
        isInst (BlockedConst _)                   = False
        isInst (PostponedTypeCheckingProblem _ _) = False
        isInst (InstV _)                          = True
        isInst (InstS _)                          = True

getOpenMetas :: TCM [MetaId]
getOpenMetas = do
    store <- getMetaStore
    return [ i | (i, MetaVar{ mvInstantiation = mi }) <- Map.assocs store, isOpen mi ]
    where
        isOpen Open                               = True
        isOpen OpenIFS                            = True
        isOpen (BlockedConst _)                   = True
        isOpen (PostponedTypeCheckingProblem _ _) = True
        isOpen (InstV _)                          = False
        isOpen (InstS _)                          = False

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

-- | Freeze all meta variables.
freezeMetas :: TCM ()
freezeMetas = modifyMetaStore $ Map.map freeze where
  freeze :: MetaVariable -> MetaVariable
  freeze mvar = mvar { mvFrozen = Frozen }

-- | Thaw all meta variables.
unfreezeMetas :: TCM ()
unfreezeMetas = modifyMetaStore $ Map.map unfreeze where
  unfreeze :: MetaVariable -> MetaVariable
  unfreeze mvar = mvar { mvFrozen = Instantiable }

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
  unfreezeMeta (Shared p)    = unfreezeMeta $ derefPtr p
  unfreezeMeta (MetaV x _)   = unfreezeMeta x
  unfreezeMeta (Sort s)      = unfreezeMeta s
  unfreezeMeta (Level l)     = unfreezeMeta l
  unfreezeMeta (DontCare t)  = unfreezeMeta t
  unfreezeMeta (Lam _ v)     = unfreezeMeta v
  unfreezeMeta _             = return ()

instance UnFreezeMeta Sort where
  unfreezeMeta (Type l)      = unfreezeMeta l
  unfreezeMeta _             = return ()

instance UnFreezeMeta Level where
  unfreezeMeta (Max ls)      = unfreezeMeta ls

instance UnFreezeMeta PlusLevel where
  unfreezeMeta (Plus _ a)    = unfreezeMeta a
  unfreezeMeta ClosedLevel{} = return ()

instance UnFreezeMeta LevelAtom where
  unfreezeMeta (MetaLevel x _)    = unfreezeMeta x
  unfreezeMeta (BlockedLevel _ t) = unfreezeMeta t
  unfreezeMeta (NeutralLevel t)   = unfreezeMeta t
  unfreezeMeta (UnreducedLevel t) = unfreezeMeta t

instance UnFreezeMeta a => UnFreezeMeta [a] where
  unfreezeMeta = mapM_ unfreezeMeta

instance UnFreezeMeta a => UnFreezeMeta (Abs a) where
  unfreezeMeta = Fold.mapM_ unfreezeMeta


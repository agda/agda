{-# LANGUAGE CPP, FlexibleInstances, TypeSynonymInstances #-}
module Agda.TypeChecking.Monad.MetaVars where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader

import Data.Maybe (isJust)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Trace
import Agda.TypeChecking.Monad.Closure
import Agda.TypeChecking.Monad.Options (reportSLn)
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Substitute

import Agda.Utils.Maybe (fromMaybeM)
import Agda.Utils.Monad ((<.>))
import Agda.Utils.Fresh
import Agda.Utils.Permutation
import Agda.Utils.Tuple
import Agda.Utils.Size

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | Switch off assignment of metas.
dontAssignMetas :: TCM a -> TCM a
dontAssignMetas = local $ \ env -> env { envAssignMetas = False }

-- | Get the meta store.
getMetaStore :: TCM MetaStore
getMetaStore = gets stMetaStore

modifyMetaStore :: (MetaStore -> MetaStore) -> TCM ()
modifyMetaStore f = modify (\ st -> st { stMetaStore = f $ stMetaStore st })

-- | Lookup a meta variable
lookupMeta :: MetaId -> TCM MetaVariable
lookupMeta m = fromMaybeM failure $ Map.lookup m <$> getMetaStore
  where failure = fail $ "no such meta variable " ++ show m

updateMetaVar :: MetaId -> (MetaVariable -> MetaVariable) -> TCM ()
updateMetaVar m f = modifyMetaStore $ Map.adjust f m

getMetaPriority :: MetaId -> TCM MetaPriority
getMetaPriority i = mvPriority <$> lookupMeta i

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

isInstantiatedMeta :: MetaId -> TCM Bool
isInstantiatedMeta m = isJust <$> isInstantiatedMeta' m

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

addInteractionPoint :: InteractionId -> MetaId -> TCM ()
addInteractionPoint ii mi = modifyInteractionPoints $ Map.insert ii mi

removeInteractionPoint :: InteractionId -> TCM ()
removeInteractionPoint ii = modifyInteractionPoints $ Map.delete ii

getInteractionPoints :: TCM [InteractionId]
getInteractionPoints = Map.keys <$> gets stInteractionPoints

getInteractionMetas :: TCM [MetaId]
getInteractionMetas = Map.elems <$> gets stInteractionPoints

-- | Does the meta variable correspond to an interaction point?

isInteractionMeta :: MetaId -> TCM (Maybe InteractionId)
isInteractionMeta x =
  lookup x . map swap . Map.assocs <$> gets stInteractionPoints

-- isInteractionMeta :: MetaId -> TCM Bool
-- isInteractionMeta m = (m `elem`) <$> getInteractionMetas

lookupInteractionId :: InteractionId -> TCM MetaId
lookupInteractionId ii =
    do  mmi <- Map.lookup ii <$> gets stInteractionPoints
	case mmi of
	    Just mi -> return mi
	    _	    -> fail $ "no such interaction point: " ++ show ii

judgementInteractionId :: InteractionId -> TCM (Judgement Type MetaId)
judgementInteractionId = mvJudgement <.> lookupMeta <=< lookupInteractionId

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

getInteractionRange :: InteractionId -> TCM Range
getInteractionRange = getMetaRange <=< lookupInteractionId

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

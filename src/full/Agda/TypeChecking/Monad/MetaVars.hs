{-# LANGUAGE CPP #-}
module Agda.TypeChecking.Monad.MetaVars where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as Map
import qualified Data.Set as Set

import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Trace
import Agda.TypeChecking.Monad.Closure
import Agda.TypeChecking.Monad.Open
import Agda.TypeChecking.Substitute

import Agda.Utils.Monad
import Agda.Utils.Fresh

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | Get the meta store.
getMetaStore :: MonadTCM tcm => tcm MetaStore
getMetaStore = gets stMetaStore

-- | Lookup a meta variable
lookupMeta :: MonadTCM tcm => MetaId -> tcm MetaVariable
lookupMeta m =
    do	mmv <- Map.lookup m <$> getMetaStore
	case mmv of
	    Just mv -> return mv
	    _	    -> fail $ "no such meta variable " ++ show m

updateMetaVar :: MonadTCM tcm => MetaId -> (MetaVariable -> MetaVariable) -> tcm ()
updateMetaVar m f =
  modify $ \st -> st { stMetaStore = Map.adjust f m $ stMetaStore st }

getMetaPriority :: MonadTCM tcm => MetaId -> tcm MetaPriority
getMetaPriority i = mvPriority <$> lookupMeta i

isSortMeta :: MonadTCM tcm => MetaId -> tcm Bool
isSortMeta m = do
  mv <- lookupMeta m
  return $ case mvJudgement mv of
    HasType{} -> False
    IsSort{}  -> True

createMetaInfo :: MonadTCM tcm => tcm MetaInfo
createMetaInfo =
    do  r <- getCurrentRange
	buildClosure r

updateMetaVarRange :: MonadTCM tcm => MetaId -> Range -> tcm ()
updateMetaVarRange mi r = updateMetaVar mi (setRange r)

addInteractionPoint :: MonadTCM tcm => InteractionId -> MetaId -> tcm ()
addInteractionPoint ii mi =
    modify $ \s -> s { stInteractionPoints =
			Map.insert ii mi $ stInteractionPoints s
		     }


removeInteractionPoint :: MonadTCM tcm => InteractionId -> tcm ()
removeInteractionPoint ii =
    modify $ \s -> s { stInteractionPoints =
			Map.delete ii $ stInteractionPoints s
		     }


getInteractionPoints :: MonadTCM tcm => tcm [InteractionId]
getInteractionPoints = Map.keys <$> gets stInteractionPoints

getInteractionMetas :: MonadTCM tcm => tcm [MetaId]
getInteractionMetas = Map.elems <$> gets stInteractionPoints

-- | Does the meta variable correspond to an interaction point?

isInteractionMeta :: MonadTCM tcm => MetaId -> tcm Bool
isInteractionMeta m = fmap (m `elem`) getInteractionMetas

lookupInteractionId :: MonadTCM tcm => InteractionId -> tcm MetaId
lookupInteractionId ii =
    do  mmi <- Map.lookup ii <$> gets stInteractionPoints
	case mmi of
	    Just mi -> return mi
	    _	    -> fail $ "no such interaction point: " ++ show ii

judgementInteractionId :: MonadTCM tcm => InteractionId -> tcm (Judgement Type MetaId)
judgementInteractionId ii =
    do  mi <- lookupInteractionId ii
        mvJudgement <$> lookupMeta mi

-- | Generate new meta variable.
newMeta :: MonadTCM tcm => MetaInfo -> MetaPriority -> Judgement Type a -> tcm MetaId
newMeta = newMeta' Open

newMeta' :: MonadTCM tcm => MetaInstantiation -> MetaInfo -> MetaPriority ->
            Judgement Type a -> tcm MetaId
newMeta' inst mi p j = do
  x <- fresh
  let mv = MetaVar mi p (fmap (const x) j) inst Set.empty
  modify $ \st -> st { stMetaStore = Map.insert x mv $ stMetaStore st }
  return x

getInteractionRange :: MonadTCM tcm => InteractionId -> tcm Range
getInteractionRange ii = do
    mi <- lookupInteractionId ii
    getMetaRange mi

getMetaRange :: MonadTCM tcm => MetaId -> tcm Range
getMetaRange mi = getRange <$> lookupMeta mi


getInteractionScope :: MonadTCM tcm => InteractionId -> tcm ScopeInfo
getInteractionScope ii =
    do mi <- lookupInteractionId ii
       mv <- lookupMeta mi
       return $ getMetaScope mv

withMetaInfo :: MonadTCM tcm => MetaInfo -> tcm a -> tcm a
withMetaInfo mI m = enterClosure mI $ \_ -> m

getInstantiatedMetas :: MonadTCM tcm => tcm [MetaId]
getInstantiatedMetas = do
    store <- getMetaStore
    return [ i | (i, MetaVar _ _ _ mi _) <- Map.assocs store, isInst mi ]
    where
	isInst Open                             = False
	isInst (BlockedConst _)                 = False
        isInst (PostponedTypeCheckingProblem _) = False
	isInst (InstV _)                        = True
	isInst (InstS _)                        = True

getOpenMetas :: MonadTCM tcm => tcm [MetaId]
getOpenMetas = do
    store <- getMetaStore
    return [ i | (i, MetaVar _ _ _ mi _) <- Map.assocs store, isOpen mi ]
    where
	isOpen Open                             = True
	isOpen (BlockedConst _)                 = True
        isOpen (PostponedTypeCheckingProblem _) = True
	isOpen (InstV _)                        = False
	isOpen (InstS _)                        = False

-- | @listenToMeta l m@: register @l@ as a listener to @m@. This is done
--   when the type of l is blocked by @m@.
listenToMeta :: MonadTCM tcm => MetaId -> MetaId -> tcm ()
listenToMeta l m =
  updateMetaVar m $ \mv -> mv { mvListeners = Set.insert l $ mvListeners mv }

-- | Unregister a listener.
unlistenToMeta :: MonadTCM tcm => MetaId -> MetaId -> tcm ()
unlistenToMeta l m =
  updateMetaVar m $ \mv -> mv { mvListeners = Set.delete l $ mvListeners mv }

-- | Get the listeners to a meta.
getMetaListeners :: MonadTCM tcm => MetaId -> tcm [MetaId]
getMetaListeners m = Set.toList . mvListeners <$> lookupMeta m

clearMetaListeners :: MonadTCM tcm => MetaId -> tcm ()
clearMetaListeners m =
  updateMetaVar m $ \mv -> mv { mvListeners = Set.empty }


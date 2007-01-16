{-# OPTIONS -cpp #-}
module TypeChecking.Monad.MetaVars where

import Control.Monad.State
import Control.Monad.Reader
import Data.Map as Map

import Syntax.Internal
import Syntax.Position
import Syntax.Scope

import TypeChecking.Monad.Base
import TypeChecking.Monad.Env
import TypeChecking.Monad.Signature
import TypeChecking.Monad.State
import TypeChecking.Monad.Trace
import TypeChecking.Monad.Closure

import Utils.Monad
import Utils.Fresh

#include "../../undefined.h"

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


createMetaInfo :: MonadTCM tcm => tcm MetaInfo
createMetaInfo = 
    do  r <- getCurrentRange
	buildClosure r

updateMetaRange :: MonadTCM tcm => MetaId -> Range -> tcm ()
updateMetaRange mi r =
    modify $ \st -> st { stMetaStore = Map.adjust (\mv -> setRange mv r) mi
				     $ stMetaStore st
		       }


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
getInteractionPoints = keys <$> gets stInteractionPoints

getInteractionMetas :: MonadTCM tcm => tcm [MetaId]
getInteractionMetas = elems <$> gets stInteractionPoints

lookupInteractionId :: MonadTCM tcm => InteractionId -> tcm MetaId
lookupInteractionId ii = 
    do  mmi <- Map.lookup ii <$> gets stInteractionPoints
	case mmi of
	    Just mi -> return mi
	    _	    -> fail $ "no such interaction point: " ++ show ii

judgementInteractionId :: MonadTCM tcm => InteractionId -> tcm (Judgement Type MetaId)
judgementInteractionId ii = 
    do  mi <- lookupInteractionId ii
        mvJudgement  <$> lookupMeta mi
        


-- | Generate new meta variable.
newMeta :: MonadTCM tcm => MetaInfo -> Judgement Type a -> tcm MetaId
newMeta mi j =
    do	x <- fresh
	let mv = MetaVar mi (fmap (const x) j) Open
	modify (\st -> st{stMetaStore = Map.insert x mv $ stMetaStore st})
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
    return [ i | (i, MetaVar _ _ mi) <- Map.assocs store, isInst mi ]
    where
	isInst Open		= False
	isInst (BlockedConst _) = False
	isInst FirstOrder	= False
	isInst (InstV _)	= True
	isInst (InstS _)	= True

getOpenMetas :: MonadTCM tcm => tcm [MetaId]
getOpenMetas = do
    store <- getMetaStore
    return [ i | (i, MetaVar _ _ mi) <- Map.assocs store, isOpen mi ]
    where
	isOpen Open		= True
	isOpen (BlockedConst _) = True
	isOpen FirstOrder	= True
	isOpen (InstV _)	= False
	isOpen (InstS _)	= False


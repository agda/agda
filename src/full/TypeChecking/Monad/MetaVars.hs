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
getMetaStore :: TCM MetaStore
getMetaStore = gets stMetaStore

-- | Lookup a meta variable
lookupMeta :: MetaId -> TCM MetaVariable
lookupMeta m =
    do	mmv <- Map.lookup m <$> getMetaStore
	case mmv of
	    Just mv -> return mv
	    _	    -> fail $ "no such meta variable " ++ show m


createMetaInfo :: TCM MetaInfo
createMetaInfo = 
    do  r <- getCurrentRange
	buildClosure r

updateMetaRange :: MetaId -> Range -> TCM ()
updateMetaRange mi r =
    modify $ \st -> st { stMetaStore = Map.adjust (\mv -> setRange mv r) mi
				     $ stMetaStore st
		       }


addInteractionPoint :: InteractionId -> MetaId -> TCM ()
addInteractionPoint ii mi =
    modify $ \s -> s { stInteractionPoints =
			Map.insert ii mi $ stInteractionPoints s
		     }


removeInteractionPoint :: InteractionId -> TCM ()
removeInteractionPoint ii =
    modify $ \s -> s { stInteractionPoints =
			Map.delete ii $ stInteractionPoints s
		     }


getInteractionPoints :: TCM [InteractionId]
getInteractionPoints = keys <$> gets stInteractionPoints

getInteractionMetas :: TCM [MetaId]
getInteractionMetas = elems <$> gets stInteractionPoints

lookupInteractionId :: InteractionId -> TCM MetaId
lookupInteractionId ii = 
    do  mmi <- Map.lookup ii <$> gets stInteractionPoints
	case mmi of
	    Just mi -> return mi
	    _	    -> fail $ "no such interaction point: " ++ show ii

judgementInteractionId :: InteractionId -> TCM (Judgement Type Sort MetaId)
judgementInteractionId ii = 
    do  mi <- lookupInteractionId ii
        mvJudgement  <$> lookupMeta mi
        


-- | Generate new meta variable.
newMeta :: MetaInfo -> Judgement Type Sort a -> TCM MetaId
newMeta mi j =
    do	x <- fresh
	let mv = MetaVar mi (fmap (const x) j) Open
	modify (\st -> st{stMetaStore = Map.insert x mv $ stMetaStore st})
	return x

getInteractionRange :: InteractionId -> TCM Range
getInteractionRange ii = do
    mi <- lookupInteractionId ii
    getMetaRange mi

getMetaRange :: MetaId -> TCM Range
getMetaRange mi = getRange <$> lookupMeta mi


getInteractionScope :: InteractionId -> TCM ScopeInfo
getInteractionScope ii = 
    do mi <- lookupInteractionId ii
       mv <- lookupMeta mi
       return $ getMetaScope mv

withMetaInfo :: MetaInfo -> TCM a -> TCM a
withMetaInfo mI m = enterClosure mI $ \_ -> m

getOpenMetas :: TCM [MetaId]
getOpenMetas = do
    store <- getMetaStore
    return [ i | (i, MetaVar _ _ Open) <- Map.assocs store ]


{-# OPTIONS -cpp #-}

module TypeChecking.Monad.Context where

import Control.Monad.Reader
import Control.Monad.State
import Data.List as List
import Data.Map as Map

import Syntax.Common
import Syntax.Internal
import TypeChecking.Monad
import TypeChecking.Substitute
import Utils.Monad

#include "../../undefined.h"

-- | add a variable to the context
--
addCtx :: Name -> Type -> TCM a -> TCM a
addCtx x a = local (\e -> e { envContext = (x,a) : raise 1 (envContext e) })
    

-- | get type of bound variable (i.e. deBruijn index)
--
typeOfBV :: Nat -> TCM Type
typeOfBV n = do
    ctx <- asks envContext
    return $ snd $ ctx !! n

getConstInfo :: QName -> TCM Definition
getConstInfo q =
    do	sig <- gets stSignature
	case Map.lookup q sig of
	    Just d  -> return d
	    _	    -> fail $ "Not in scope: " ++ show q

-- | get type of a constant 
--
typeOfConst :: QName -> TCM Type
typeOfConst q = defType <$> getConstInfo q


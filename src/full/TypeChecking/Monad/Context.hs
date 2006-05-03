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

-- | Get the name of the current module.
currentModule :: TCM ModuleName
currentModule = asks envCurrentModule

-- | Set the name of the current module.
withCurrentModule :: ModuleName -> TCM a -> TCM a
withCurrentModule m =
    local $ \e -> e { envCurrentModule = m }

-- | add a variable to the context
--
addCtx :: Name -> Type -> TCM a -> TCM a
addCtx x a = local (\e -> e { envContext = (x,a) : raise 1 (envContext e) })

-- | add a bunch of variables with the same type to the context
addCtxs :: [Name] -> Type -> TCM a -> TCM a
addCtxs []     _ k = k
addCtxs (x:xs) t k = addCtx x t $ addCtxs xs (raise 1 t) k

-- | Add a constant to the signature.
addConstant :: QName -> Definition -> TCM ()
addConstant q d = modify $ \s -> s { stSignature = Map.insert q d $ stSignature s }

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


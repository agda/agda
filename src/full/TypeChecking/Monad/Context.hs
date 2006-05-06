{-# OPTIONS -cpp #-}

module TypeChecking.Monad.Context where

import Control.Monad.Reader
import Control.Monad.State
import Data.List as List
import Data.Map as Map

import Syntax.Common
import Syntax.Internal
import Syntax.Position
import TypeChecking.Monad
import TypeChecking.Substitute
import Utils.Monad

#include "../../undefined.h"

-- | Get the name of the current module, if any.
currentModule :: TCM (Maybe ModuleName)
currentModule = asks envCurrentModule

-- | Get the name of the current module. Assumes there is one.
currentModule_ :: TCM ModuleName
currentModule_ =
    do	m <- currentModule
	case m of
	    Just m  -> return m
	    Nothing -> fail "panic: no current module!"

-- | Set the name of the current module.
withCurrentModule :: ModuleName -> TCM a -> TCM a
withCurrentModule m =
    local $ \e -> e { envCurrentModule = Just m }

-- | add a variable to the context
--
addCtx :: Name -> Type -> TCM a -> TCM a
addCtx x a = local (\e -> e { envContext = (x,a) : envContext e })

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
    return $ raise (n + 1) $ snd $ ctx !! n

-- | Get the deBruijn index of a named variable
varIndex :: Name -> TCM Nat
varIndex x =
    do	ctx <- asks envContext
	case List.findIndex ((==x) . fst) ctx of
	    Just n  -> return n
	    _	    -> fail $ "unbound variable " ++ show x

getConstInfo :: QName -> TCM Definition
getConstInfo q =
    do	sig <- gets stSignature
	case Map.lookup q sig of
	    Just d  -> return d
	    _	    -> fail $ show (getRange q) ++ ": not in scope " ++ show q ++ " in " ++ show sig

-- | get type of a constant 
--
typeOfConst :: QName -> TCM Type
typeOfConst q = defType <$> getConstInfo q


escapeContext :: Int -> TCM a -> TCM a
escapeContext n = local $ \e -> e { envContext = drop n $ envContext e }


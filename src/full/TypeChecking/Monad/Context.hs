{-# OPTIONS -cpp #-}

module TypeChecking.Monad.Context where

import Control.Monad.Reader
import Data.List as List

import Syntax.Abstract.Name
import Syntax.Common
import Syntax.Internal
import Syntax.Scope

import TypeChecking.Monad.Base
import TypeChecking.Substitute

import Utils.Monad

#include "../../undefined.h"

-- | add a variable to the context
--
addCtx :: Name -> Type -> TCM a -> TCM a
addCtx x a = local (\e -> e { envContext = (x,a) : envContext e })

-- | Get the current context.
getContext :: TCM Context
getContext = asks envContext

-- | Get the current context as a 'Telescope' (everything 'Hidden').
getContextTelescope :: TCM Telescope
getContextTelescope = List.map (Arg Hidden . snd) . reverse <$> getContext

-- | add a bunch of variables with the same type to the context
addCtxs :: [Name] -> Type -> TCM a -> TCM a
addCtxs []     _ k = k
addCtxs (x:xs) t k = addCtx x t $ addCtxs xs (raise 1 t) k

-- | Add a telescope to the context. Uses dummy names.
addCtxTel :: Telescope -> TCM a -> TCM a
addCtxTel [] ret = ret
addCtxTel (Arg _ t : tel) ret =
    do	x <- freshNoName_
	addCtx x t $ addCtxTel tel ret

-- | get type of bound variable (i.e. deBruijn index)
--
typeOfBV :: Nat -> TCM Type
typeOfBV n =
    do	ctx <- getContext
	(_,t) <- ctx !!! n
	return $ raise (n + 1) t

nameOfBV :: Nat -> TCM Name
nameOfBV n =
    do	ctx <- getContext
	(x,_) <- ctx !!! n
	return x

-- | TODO: move(?)
xs !!! n = xs !!!! n
    where
	[]     !!!! _ = fail $ "deBruijn index out of scope: " ++ show n
	(x:_)  !!!! 0 = return x
	(_:xs) !!!! n = xs !!!! (n - 1)

-- | Get the deBruijn index of a named variable
varIndex :: Name -> TCM Nat
varIndex x =
    do	ctx <- asks envContext
	case List.findIndex ((==x) . fst) ctx of
	    Just n  -> return n
	    _	    -> fail $ "unbound variable " ++ show x

escapeContext :: Int -> TCM a -> TCM a
escapeContext n = local $ \e -> e { envContext = drop n $ envContext e }


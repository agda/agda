{-# OPTIONS -cpp #-}

module TypeChecking.Monad.Context where

import Control.Monad.Reader
import Data.List as List
import Data.Map as Map

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
addCtx x a = local $ \e ->
		e { envContext	   = (x,a) : envContext e
		  , envLetBindings = raise 1 $ envLetBindings e
		  }

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

-- | Add a let bound variable
addLetBinding :: Name -> Term -> Type -> TCM a -> TCM a
addLetBinding x v t =
    local $ \e -> e { envLetBindings = Map.insert x (v,t) $ envLetBindings e }

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

-- | Get the term corresponding to a named variable. If it is a lambda bound
--   variable the deBruijn index is returned and if it is a let bound variable
--   its definition is returned.
getVarInfo :: Name -> TCM (Term, Type)
getVarInfo x =
    do	ctx <- asks envContext
	def <- asks envLetBindings
	case List.findIndex ((==x) . fst) ctx of
	    Just n  ->
		do  t <- typeOfBV n
		    return (Var n [], t)
	    _	    ->
		case Map.lookup x def of
		    Just vt -> return vt
		    _	    -> fail $ "unbound variable " ++ show x

escapeContext :: Int -> TCM a -> TCM a
escapeContext n = local $ \e -> e { envContext = drop n $ envContext e }


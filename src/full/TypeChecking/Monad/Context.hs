{-# OPTIONS -cpp #-}

module TypeChecking.Monad.Context where

import Control.Monad.Reader
import Data.List
import qualified Data.Map as Map

import Syntax.Abstract.Name
import Syntax.Common
import Syntax.Internal
import Syntax.Scope.Base

import TypeChecking.Monad.Base
import TypeChecking.Substitute
import TypeChecking.Monad.Open

import Utils.Monad

#include "../../undefined.h"

-- | add a variable to the context
--
addCtx :: MonadTCM tcm => Name -> Type -> tcm a -> tcm a
addCtx x a = local $ \e ->
		e { envContext	   = (x,a) : envContext e
		  } -- let-bindings keep track of their context

-- | Change the context
inContext :: MonadTCM tcm => Context -> tcm a -> tcm a
inContext ctx = local $ \e -> e { envContext = ctx }

-- | Go under an abstraction.
underAbstraction :: MonadTCM tcm => Type -> Abs a -> (a -> tcm b) -> tcm b
underAbstraction t a k = do
    x <- freshName_ $ absName a
    addCtx x t $ k $ absBody a

-- | Get the current context.
getContext :: MonadTCM tcm => tcm Context
getContext = asks envContext

-- | Generate [Var n - 1, .., Var 0] for all declarations in the context.
getContextArgs :: MonadTCM tcm => tcm Args
getContextArgs = map (Arg NotHidden) <$> getContextTerms

getContextTerms :: MonadTCM tcm => tcm [Term]
getContextTerms = do
  ctx <- getContext
  return $ reverse $ map (\i -> Var i []) $ [0 .. length ctx - 1]

-- | Get the current context as a 'Telescope' (everything 'Hidden').
getContextTelescope :: MonadTCM tcm => tcm Telescope
getContextTelescope = getContextTelescope' Hidden

-- | Get the current context as a 'Telescope' with the specified 'Hiding'.
getContextTelescope' :: MonadTCM tcm => Hiding -> tcm Telescope
getContextTelescope' h = foldr extTel EmptyTel . reverse <$> getContext
  where
    extTel (x, t) = ExtendTel (Arg h t) . Abs (show x)

-- | add a bunch of variables with the same type to the context
addCtxs :: MonadTCM tcm => [Name] -> Type -> tcm a -> tcm a
addCtxs []     _ k = k
addCtxs (x:xs) t k = addCtx x t $ addCtxs xs (raise 1 t) k

-- | Add a telescope to the context.
addCtxTel :: MonadTCM tcm => Telescope -> tcm a -> tcm a
addCtxTel EmptyTel	    ret = ret
addCtxTel (ExtendTel t tel) ret = do
  x <- freshName_ $ absName tel
  addCtx x (unArg t) $ addCtxTel (absBody tel) ret

-- | Add a let bound variable
addLetBinding :: MonadTCM tcm => Name -> Term -> Type -> tcm a -> tcm a
addLetBinding x v t ret = do
    vt <- makeOpen (v, t)
    flip local ret $ \e -> e { envLetBindings = Map.insert x vt $ envLetBindings e }

-- | get type of bound variable (i.e. deBruijn index)
--
typeOfBV :: MonadTCM tcm => Nat -> tcm Type
typeOfBV n =
    do	ctx <- getContext
	(_,t) <- ctx !!! n
	return $ raise (n + 1) t

nameOfBV :: MonadTCM tcm => Nat -> tcm Name
nameOfBV n =
    do	ctx <- getContext
	(x,_) <- ctx !!! n
	return x

-- | TODO: move(?)
xs !!! n = xs !!!! n
    where
	[]     !!!! _ = do
            ctx <- getContext
            fail $ "deBruijn index out of scope: " ++ show n ++ " in context " ++ show (map fst ctx)
	(x:_)  !!!! 0 = return x
	(_:xs) !!!! n = xs !!!! (n - 1)

-- | Get the term corresponding to a named variable. If it is a lambda bound
--   variable the deBruijn index is returned and if it is a let bound variable
--   its definition is returned.
getVarInfo :: MonadTCM tcm => Name -> tcm (Term, Type)
getVarInfo x =
    do	ctx <- getContext
	def <- asks envLetBindings
	case findIndex ((==x) . fst) ctx of
	    Just n  ->
		do  t <- typeOfBV n
		    return (Var n [], t)
	    _	    ->
		case Map.lookup x def of
		    Just vt -> getOpen vt
		    _	    -> fail $ "unbound variable " ++ show x

escapeContext :: MonadTCM tcm => Int -> tcm a -> tcm a
escapeContext n = local $ \e -> e { envContext = drop n $ envContext e }


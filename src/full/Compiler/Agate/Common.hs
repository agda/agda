{-# OPTIONS -fglasgow-exts -cpp #-}

#include "../../undefined.h"

{-| common
-}

module Compiler.Agate.Common where

import Control.Monad

import Compiler.Agate.TranslateName

import Syntax.Common
import Syntax.Literal
import Syntax.Internal

import TypeChecking.Monad
import TypeChecking.Reduce

import Utils.Pretty
import Utils.Monad

----------------------------------------------------------------

psep :: [Doc] -> Doc
psep [x] = x
psep xs = parens $ sep xs


dropArgs :: Int -> Type -> TCM Type
dropArgs n (El s t) = dropArgsTm s n t
    where
	dropArgsTm s 0 t = return (El s t)
	dropArgsTm _ n t = do
	    t <- reduce t
	    case ignoreBlocking t of
		Pi arg abs  -> dropArgs (n - 1) $ absBody abs
		Fun arg ty  -> dropArgs (n - 1) ty
		Var _ _	    -> __IMPOSSIBLE__
		Def _ _	    -> __IMPOSSIBLE__
		Con _ _	    -> __IMPOSSIBLE__
		MetaV _ _   -> __IMPOSSIBLE__
		Lam _ _	    -> __IMPOSSIBLE__
		Sort _	    -> __IMPOSSIBLE__
		Lit _	    -> __IMPOSSIBLE__
		BlockedV _  -> __IMPOSSIBLE__

withFunctionDomain :: Type -> (Type -> TCM a) -> ([a] -> Type -> TCM b) -> TCM b
withFunctionDomain (El s tm) f ret = withDomain s tm
    where
	withDomain s tm = do
	    tm <- reduce tm
	    case tm of
		Pi arg abs -> do
		    res	    <- f $ unArg arg
		    underAbstraction (unArg arg) abs $ \ty ->
			withFunctionDomain ty f $ \ress ty ->
			ret (res : ress) ty
		Fun arg ty -> do
		    res  <- f $ unArg arg
		    withFunctionDomain ty f $ \ress ty ->
			ret (res : ress) ty
		Var _ _    -> ret [] (El s tm)
		Def _ _    -> ret [] (El s tm)
		Con _ _    -> ret [] (El s tm)
		Sort _	   -> ret [] (El s tm)
		Lit _	   -> __IMPOSSIBLE__
		MetaV _ _  -> __IMPOSSIBLE__
		Lam _ _	   -> __IMPOSSIBLE__
		BlockedV _ -> __IMPOSSIBLE__

splitType :: Type -> TCM ([Type], Type)
splitType ty = withFunctionDomain ty return $ \tys ty -> return (tys,ty)

forEachArgM :: (Type -> TCM a) -> Type -> TCM [a]
forEachArgM f ty = withFunctionDomain ty f $ \ress _ -> return ress

underContext :: Type -> TCM a -> TCM a
underContext ty k = withFunctionDomain ty return $ \_ _ -> k

showLiteralContent :: Literal -> String
showLiteralContent (LitInt    _ i) = show i
showLiteralContent (LitString _ s) = show s
showLiteralContent (LitFloat  _ f) = show f
showLiteralContent (LitChar   _ c) = show c

--

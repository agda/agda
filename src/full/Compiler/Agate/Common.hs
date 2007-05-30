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
import TypeChecking.Substitute

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
	    case ignoreBlocking tm of
		Pi arg abs -> do
		    res	    <- f $ unArg arg
		    underAbstraction arg abs $ \ty ->
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

--

showOptimizedLiteral :: Literal -> Doc
showOptimizedLiteral (LitInt    _ i) = text $ show i
showOptimizedLiteral (LitString _ s) = text $ show s
showOptimizedLiteral (LitFloat  _ f) = text $ show f
showOptimizedLiteral (LitChar   _ c) = text $ show c

showUntypedLiteral :: Literal -> Doc
showUntypedLiteral (LitInt    _ i) = text "VInt"    <+> text (show i)
showUntypedLiteral (LitString _ s) = text "VString" <+> text (show s)
showUntypedLiteral (LitFloat  _ f) = text "VFloat"  <+> text (show f)
showUntypedLiteral (LitChar   _ c) = text "VChar"   <+> text (show c)

--


{-# OPTIONS -fglasgow-exts -cpp #-}

{-| common
-}

module Agda.Compiler.Agate.Common where

#include "../../undefined.h"
import Agda.Utils.Impossible

import Control.Monad

import Agda.Compiler.Agate.TranslateName

import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

import Agda.Utils.Pretty
import Agda.Utils.Monad

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


showClause :: (Term -> TCM Doc) ->
	      (QName -> [Doc] -> TCM Doc) ->
	      ([Doc] -> Term -> TCM Doc) -> Clause -> TCM Doc
showClause fTerm fCon fBody (Clause _ _ pats NoBody) = return empty
showClause fTerm fCon fBody (Clause _ _ pats body)   = go 0 [] body
    where
    go :: Int -> [Doc] -> ClauseBody -> TCM Doc
    go n dvars NoBody        = return empty
    go n dvars (NoBind body) = go n (dvars ++ [text "_"]) body
    go n dvars (Bind abs)    =
	underAbstraction_ abs{absName = show (n + 1)} $ \body -> do
	    dvar <- fTerm $ Var 0 []
	    go (n + 1) (dvars ++ [dvar]) body
    go n dvars (Body term)   = do
	(_,dpats) <- showPatterns dvars $ map unArg pats
	fBody dpats term

    showPatterns :: [Doc] -> [Pattern] -> TCM ([Doc], [Doc])
    showPatterns dvars []           = return (dvars,[])
    showPatterns dvars (pat : pats) = do
	(dvars', dpat)  <- showPattern  dvars  pat
	(dvars'',dpats) <- showPatterns dvars' pats
	return (dvars'', (dpat : dpats))

    showPattern :: [Doc] -> Pattern -> TCM ([Doc], Doc)
    showPattern (dvar : dvars) (VarP s) = return (dvars, dvar)
    showPattern []             (VarP s) = __IMPOSSIBLE__
    showPattern (dvar : dvars) (DotP _) = return (dvars, dvar)
    showPattern []             (DotP _) = __IMPOSSIBLE__
    showPattern dvars (ConP name args) = do
	(dvars',dargs) <- showPatterns dvars (map unArg args)
	dcon <- fCon name dargs
	return (dvars', dcon)
    showPattern dvars (LitP lit) = do
	dlit <- fTerm $ Lit lit
	return (dvars, dlit)

--


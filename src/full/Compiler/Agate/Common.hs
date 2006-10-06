{-# OPTIONS -fglasgow-exts -cpp #-}

#include "../../undefined.h"

{-| common
-}

module Compiler.Agate.Common where

import Compiler.Agate.TranslateName

import Syntax.Common
import Syntax.Literal
import Syntax.Internal
import TypeChecking.Monad
import Utils.Pretty

----------------------------------------------------------------

psep :: [Doc] -> Doc
psep [x] = x
psep xs = parens $ sep xs


dropArgs :: Int -> Type -> TCM Type
dropArgs 0 ty              = return ty
dropArgs n (El t s)        = return __IMPOSSIBLE__
dropArgs n (Pi arg abs)    = dropArgs (n - 1) $ absBody abs
dropArgs n (Fun arg ty)    = dropArgs (n - 1) $ ty
dropArgs n (Sort s)        = return __IMPOSSIBLE__
dropArgs n (MetaT id args) = return __IMPOSSIBLE__
dropArgs n (LamT abs)      = return __IMPOSSIBLE__

splitType :: Type -> TCM ([Type],Type)
splitType (El t s) = return ([],El t s)
splitType (Pi arg abs) = do
    (tys,res) <- splitType $ absBody abs
    return (unArg arg : tys, res)
splitType (Fun arg ty) = do
    (tys,res) <- splitType ty
    return (unArg arg : tys, res)
splitType (Sort s)        = return ([],Sort s)
splitType (MetaT id args) = return __IMPOSSIBLE__
splitType (LamT abs)      = return __IMPOSSIBLE__

forEachArgM :: (Type -> TCM a) -> Type -> TCM [a]
forEachArgM f (El t s)     = return [] -- assumes Pi not in Set
forEachArgM f (Pi arg abs) = do
    newname <- freshName_ $ absName abs
    res <- f $ unArg arg
    addCtx newname (unArg arg) $ do
	ress <- forEachArgM f (absBody abs)
	return (res : ress)
forEachArgM f (Fun arg ty) = do
    res <- f $ unArg arg
    ress <- forEachArgM f ty
    return (res : ress)
forEachArgM f (Sort s)        = return []
forEachArgM f (MetaT id args) = return __IMPOSSIBLE__
forEachArgM f (LamT abs)      = return __IMPOSSIBLE__

underContext :: Type -> TCM a -> TCM a
underContext (El t s)        k = k -- assumes Pi not in Set
underContext (Pi arg abs)    k =
    underAbstraction (unArg arg) abs $ flip underContext k
underContext (Fun arg ty)    k = underContext ty k
underContext (Sort s)        k = k
underContext (MetaT id args) k = return __IMPOSSIBLE__
underContext (LamT abs)      k = return __IMPOSSIBLE__

showLiteralContent :: Literal -> String
showLiteralContent (LitInt    _ i) = show i
showLiteralContent (LitString _ s) = show s
showLiteralContent (LitFloat  _ f) = show f
showLiteralContent (LitChar   _ c) = show c

--

{-# OPTIONS -fglasgow-exts -cpp #-}

#include "../../undefined.h"

{-| common
-}

module Compiler.Agate.Common where

import Compiler.Agate.TranslateName
import TypeChecking.MetaVars

import Char(isDigit,intToDigit,isAlpha,isLower,isUpper,ord)
import GHC.Base (map)

import Syntax.Internal
import Syntax.Scope
import Text.PrettyPrint
import Syntax.Common
{-
import Control.Monad.State
import Control.Monad.Error
-}

import Data.List as List
import Data.Map as Map
import Data.Maybe
{-
import System.Environment
import System.IO
import System.Exit
-}

import Syntax.Parser
import Syntax.Concrete.Pretty ()
import qualified Syntax.Abstract as A
import Syntax.Translation.ConcreteToAbstract
import Syntax.Translation.AbstractToConcrete
import Syntax.Translation.InternalToAbstract
import Syntax.Abstract.Test
import Syntax.Abstract.Name
import Syntax.Strict
import Syntax.Literal


import Interaction.Exceptions
import Interaction.CommandLine.CommandLine
import Interaction.EmacsInterface.EmacsAgda
import Interaction.Options
import Interaction.Monad
import Interaction.GhciTop ()	-- to make sure it compiles

import TypeChecker
import TypeChecking.Monad
import TypeChecking.Reduce
import TypeChecking.Errors
{-
import Utils.Monad

import Version
-}


----------------------------------------------------------------

psep :: [Doc] -> Doc
psep [x] = x
psep xs = parens $ sep xs


dropArgs :: Int -> Type -> IM Type
dropArgs 0 ty              = return ty
dropArgs n (El t s)        = return __IMPOSSIBLE__
dropArgs n (Pi arg abs)    = dropArgs (n - 1) $ absBody abs
dropArgs n (Fun arg ty)    = dropArgs (n - 1) $ ty
dropArgs n (Sort s)        = return __IMPOSSIBLE__
dropArgs n (MetaT id args) = return __IMPOSSIBLE__
dropArgs n (LamT abs)      = return __IMPOSSIBLE__

splitType :: Type -> IM ([Type],Type)
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

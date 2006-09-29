{-# OPTIONS -fglasgow-exts -cpp #-}

#include "../../undefined.h"

{-| Generate GHC code for untyped execution
-}

module Compiler.Agate.UntypedPrinter where

import Compiler.Agate.TranslateName
import Compiler.Agate.Common
import Compiler.Agate.OptimizedPrinter

import Char(isDigit,intToDigit,isAlpha,isLower,isUpper,ord)
import GHC.Base (map)

import Syntax.Internal
import Syntax.Scope
import Text.PrettyPrint
import Syntax.Common

import Control.Monad.State
import Control.Monad.Error

import Data.List as List
import Data.Map as Map
import Data.Maybe

import System.Environment
import System.IO
import System.Exit

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

import Utils.Monad

import Version


----------------------------------------------------------------
-- implementation of the "X" function

class ShowAsUntypedTerm a where
    showAsUntypedTerm :: a -> IM Doc 

instance ShowAsUntypedTerm Name where
    showAsUntypedTerm t = return $ text $ translateNameAsUntypedTerm t

instance ShowAsUntypedTerm QName where
    showAsUntypedTerm t = return $ text $ translateNameAsUntypedTerm t

instance ShowAsUntypedTerm Term where
    showAsUntypedTerm (Var n args) =
     do varname <- nameOfBV n
    	dvar <- showAsUntypedTerm varname
    	dargs <- mapM showAsUntypedTerm (GHC.Base.map unArg args)
        return $ foldl (\f a -> parens (f <+> text "|$|" <+> a)) dvar dargs
    showAsUntypedTerm (Lam h abs@(Abs v b)) =
     do newname <- freshName_ (absName abs)
	addCtx newname __IMPOSSIBLE__ $ do
	    dvar <- showAsUntypedTerm $ Var 0 []
	    dbody <- showAsUntypedTerm (absBody abs)
	    return $ parens $ text "VAbs" <+>
		     parens (sep [ text "\\" <> dvar, text "->", dbody ])
    showAsUntypedTerm (Con nm as) =
     do dnm <- showQNameAsUntypedConstructor nm
        das <- mapM showAsUntypedTerm (GHC.Base.map unArg as)
        return $ parens $ text "VCon" <> text (show (length as)) <+> dnm <+> hsep das
    showAsUntypedTerm (Def qname args) =
     do dname <- showAsUntypedTerm qname
    	dargs <- mapM showAsUntypedTerm (GHC.Base.map unArg args)
        return $ foldl (\f a -> parens (f <+> text "|$|" <+> a)) dname dargs
    showAsUntypedTerm (Lit (LitInt    _ i)) = return $ parens $ text "VInt" <+> text (show i)
    showAsUntypedTerm (Lit (LitString _ s)) = return $ parens $ text "VString" <+> text (show s)
    showAsUntypedTerm (Lit (LitFloat  _ f)) = return $ parens $ text "VFloat" <+> text (show f)
    showAsUntypedTerm (Lit (LitChar   _ c)) = return $ parens $ text "VChar" <+> text (show c)
    showAsUntypedTerm _ = return __IMPOSSIBLE__

instance ShowAsUntypedTerm ClauseBody where
    showAsUntypedTerm (Body t)      = showAsUntypedTerm t
    showAsUntypedTerm (Bind abs)    = do
	newname <- freshName_ (absName abs)
	addCtx newname __IMPOSSIBLE__ $ showAsUntypedTerm (absBody abs)
    showAsUntypedTerm (NoBind body) = showAsUntypedTerm body
    showAsUntypedTerm NoBody        = return $ text "(absurd)"



showAsUntypedConstructor :: Name -> IM Doc
showAsUntypedConstructor name =
    return $ text $ translateNameAsUntypedConstructor name

showQNameAsUntypedConstructor :: QName -> IM Doc
showQNameAsUntypedConstructor qname =
    return $ text $ translateNameAsUntypedConstructor qname


----------------------------------------------------------------

class ShowAsUntyped a where
    showAsUntyped :: a -> IM Doc 

instance ShowAsUntyped Pattern where
    showAsUntyped (VarP s)          =
	return $ text $ translateNameAsUntypedTerm (VarP s)
    showAsUntyped (ConP qname args) = do
	dname <- showQNameAsUntypedConstructor qname
	dargs <- mapM (showAsUntyped . unArg) args
	return $ parens $ (text "VCon" <> text (show (length dargs))) <+>
			  sep (dname : dargs)
    showAsUntyped (LitP lit) = return $ text "Literal" -- TODO: not allowed?
    showAsUntyped AbsurdP    = return $ text "()"      -- __IMPOSSIBLE__

showClause :: Clause -> IM Doc
showClause (Clause pats NoBody) = return Text.PrettyPrint.empty
showClause (Clause pats body)   = do
    dpats <- mapM (showAsUntyped . unArg) pats 
    dbody <- showAsUntypedTerm body
    return $ text "f" <+>
	     sep [ sep [ sep dpats, equals ], dbody ]

----------------------------------------------------------------

showNDefinition :: (Name,Definition) -> IM Doc
showNDefinition (name,defn) = do
    dname <- showAsUntypedTerm name
    case theDef defn of
      Axiom -> do
	return $ sep [ dname, equals ] <+>
		 sep [ text "undefined {- postulate -}" ]
      Function [] a -> return $ text "return __IMPOSSIBLE__"
      Function clauses a -> do
        let (Clause pats body) = head clauses
	let patsize = length pats
	let dvars = GHC.Base.map (\i -> text ("v" ++ show i)) [1..patsize]
	let drhs = untypedAbs dvars $ sep (text "f" : dvars)
	dclauses <- mapM showClause clauses
	return $ (dname <+> equals) <+> drhs <+> text "where" $+$
		 nest 2 (vcat dclauses)
      Datatype np qcnames s a -> do
	ty <- instantiate $ defType defn
	(args,_) <- splitType ty
	let dvars = GHC.Base.map (\i -> text ("v" ++ show i)) [1..np]
	let drhs = untypedAbs dvars $ text "VNonData"
	return $ sep [ dname, equals ] <+> drhs <+> text "{- datatype -}"
      Constructor np qtname a -> do
	dcname <- showAsUntypedConstructor name
	ty <- instantiate $ defType defn
	(args,_) <- splitType ty
	let argsize = length args - np
	let dvars = GHC.Base.map (\i -> text ("v" ++ show i)) [1..argsize]
	let drhs = untypedAbs dvars $ sep $
		    text "VCon" <> text (show argsize) : dcname : dvars
	return $ sep [ dname, equals ] <+> drhs
      Primitive a pf -> do
	doname <- showAsOptimizedTerm name
	return $ sep [ dname, equals ] <+>
		 sep [ text "box", doname, text "{- primitive -}" ]

untypedAbs :: [Doc] -> Doc -> Doc
untypedAbs dvars dtail = foldr
    (\dvar d -> sep [ text "VAbs (\\" <> dvar <+> text "->",
		      d <> text ")" ]) dtail dvars

----------------------------------------------------------------
--
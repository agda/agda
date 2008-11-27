{-# LANGUAGE CPP #-}

{-| Generate GHC code for untyped execution
-}

module Agda.Compiler.Agate.UntypedPrinter where

import Data.List

#include "../../undefined.h"
import Agda.Utils.Impossible

import Agda.Compiler.Agate.TranslateName
import Agda.Compiler.Agate.Common
import Agda.Compiler.Agate.OptimizedPrinter

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.Utils.Pretty

----------------------------------------------------------------

showAsUntypedConstructor :: QName -> TCM Doc
showAsUntypedConstructor name =
    return $ text $ translateNameAsUntypedConstructor $ show name

----------------------------------------------------------------
-- implementation of the "X" function

class ShowAsUntypedTerm a where
    showAsUntypedTerm :: a -> TCM Doc 

instance ShowAsUntypedTerm Name where
    showAsUntypedTerm t = return $ text $ translateNameAsUntypedTerm $ show t

instance ShowAsUntypedTerm QName where
    showAsUntypedTerm t = return $ text $ translateNameAsUntypedTerm $ show t

instance ShowAsUntypedTerm Term where
    showAsUntypedTerm (Var n args) = do
	varname <- nameOfBV n
	showUntypedApp varname args
    showAsUntypedTerm (Lam h abs) = underAbstraction_ abs $ \body -> do
	dvar <- showAsUntypedTerm $ Var 0 []
	dbody <- showAsUntypedTerm body
	return $ parens $ text "VAbs" <+>
		 parens (sep [ text "\\" <> dvar, text "->", dbody ])
    showAsUntypedTerm (Con name args) = showUntypedApp name args
    showAsUntypedTerm (Def name args) = showUntypedApp name args
    showAsUntypedTerm (Lit lit)    = return $ parens $ showUntypedLiteral lit
    showAsUntypedTerm (Pi _ _)	   = return $ text "VNonData"
    showAsUntypedTerm (Fun _ _)    = return $ text "VNonData"
    showAsUntypedTerm (Sort _)	   = return $ text "VNonData"
    showAsUntypedTerm (MetaV _ _)  = __IMPOSSIBLE__

showUntypedApp :: ShowAsUntypedTerm a => a -> [Arg Term] -> TCM Doc
showUntypedApp head args = do
    dhead <- showAsUntypedTerm head
    dargs <- mapM (showAsUntypedTerm . unArg) args
    return $ foldl (\f a -> parens (f <+> text "|$|" <+> a)) dhead dargs

----------------------------------------------------------------

showUntypedDefinition :: (QName, Definition) -> TCM Doc
showUntypedDefinition (name, defn) = do
    dname <- showAsUntypedTerm name
    case theDef defn of
	Axiom{} ->
	    return $ sep [ dname, equals ] <+>
		     sep [ text "undefined {- postulate -}" ]
	Function {funClauses = []} -> __IMPOSSIBLE__
	Function {funClauses = clauses} -> do
            let (Clause _ _ pats body) = head clauses
	    let dvars = map (\i -> text ("v" ++ show i)) [1 .. length pats]
	    let drhs = untypedAbs dvars $ sep (text "f" : dvars)
	    dclauses <- mapM showUntypedClause clauses
	    return $ (dname <+> equals) <+> drhs <+> text "where" $+$
		     nest 2 (vcat dclauses)
	Datatype{ dataPars = np, dataIxs = ni, dataCons = cnames } -> do
	    let dvars = map (\i -> text ("v" ++ show i)) [1 .. np + ni]
	    let drhs = untypedAbs dvars $ text "VNonData"
	    return $ sep [ dname, equals ] <+> drhs <+> text "{- datatype -}"
	Record{ recPars = np, recFields = flds } -> do
	    dcname <- showAsUntypedConstructor name
	    let arity = length flds
	    let dvars = map (\i -> text ("v" ++ show i)) [1 .. arity]
	    let drhs = untypedAbs dvars $ sep $
		       text "VCon" <> text (show arity) : dcname : dvars
	    return $ sep [ dname, equals ] <+> drhs
	Constructor{ conPars = np } -> do
	    dcname <- showAsUntypedConstructor name
	    ty <- instantiate $ defType defn
	    (args,_) <- splitType ty
	    let arity = genericLength args - np
	    let dvars = map (\i -> text ("v" ++ show i)) [1 .. arity]
	    let drhs = untypedAbs dvars $ sep $
		       text "VCon" <> text (show arity) : dcname : dvars
	    return $ sep [ dname, equals ] <+> drhs
	Primitive{ primName = pf } -> do
	    doptname <- showAsOptimizedTerm name
	    return $ sep [ dname, equals ] <+>
		     sep [ text "box", doptname, text "{- primitive -}" ]

untypedAbs :: [Doc] -> Doc -> Doc
untypedAbs dvars dtail = foldr
    (\dvar d -> sep [ text "VAbs (\\" <> dvar <+> text "->",
		      d <> text ")" ]) dtail dvars

showUntypedClause :: Clause -> TCM Doc
showUntypedClause = showClause fTerm fCon fBody where
    fTerm = showAsUntypedTerm
    fCon name dargs = do
	dname <- showAsUntypedConstructor name
	return $ parens $ (text "VCon" <> text (show (length dargs))) <+>
			  sep (dname : dargs)
    fBody dpats term = do
	dterm <- showAsUntypedTerm term
	return $ text "f" <+> sep [ sep [ sep dpats, equals ], dterm ]

----------------------------------------------------------------
--

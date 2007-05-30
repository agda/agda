{-# OPTIONS -fglasgow-exts -cpp #-}

#include "../../undefined.h"

{-| Generate GHC code for untyped execution
-}

module Compiler.Agate.UntypedPrinter where

import Compiler.Agate.TranslateName
import Compiler.Agate.Common
import Compiler.Agate.OptimizedPrinter

import Syntax.Common
import Syntax.Internal
import Syntax.Literal
import TypeChecking.Monad
import TypeChecking.Reduce
import Utils.Pretty

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
	dvar <- showAsUntypedTerm varname
	dargs <- mapM (showAsUntypedTerm . unArg) args
	return $ foldl (\f a -> parens (f <+> text "|$|" <+> a)) dvar dargs
    showAsUntypedTerm (Lam h abs) = underAbstraction_ abs $ \body -> do
	dvar <- showAsUntypedTerm $ Var 0 []
	dbody <- showAsUntypedTerm body
	return $ parens $ text "VAbs" <+>
		 parens (sep [ text "\\" <> dvar, text "->", dbody ])
    showAsUntypedTerm (Con qname args) = do
	dname <- showAsUntypedTerm qname
	dargs <- mapM (showAsUntypedTerm . unArg) args
	return $ foldl (\f a -> parens (f <+> text "|$|" <+> a)) dname dargs
    showAsUntypedTerm (Def qname args) = do
	dname <- showAsUntypedTerm qname
	dargs <- mapM (showAsUntypedTerm . unArg) args
	return $ foldl (\f a -> parens (f <+> text "|$|" <+> a)) dname dargs
    showAsUntypedTerm (Lit lit)    = return $ parens $ showUntypedLiteral lit
    showAsUntypedTerm (Pi _ _)	   = return $ text "VNonData"
    showAsUntypedTerm (Fun _ _)    = return $ text "VNonData"
    showAsUntypedTerm (Sort _)	   = return $ text "VNonData"
    showAsUntypedTerm (MetaV _ _)  = __IMPOSSIBLE__
    showAsUntypedTerm (BlockedV _) = __IMPOSSIBLE__

----------------------------------------------------------------

showUntypedDefinition :: (QName, Definition) -> TCM Doc
showUntypedDefinition (name, defn) = do
    dname <- showAsUntypedTerm name
    case theDef defn of
      Axiom ->
	return $ sep [ dname, equals ] <+>
		 sep [ text "undefined {- postulate -}" ]
      Function [] a -> return $ text "return __IMPOSSIBLE__"
      Function clauses a -> do
        let (Clause pats body) = head clauses
	let dvars = map (\i -> text ("v" ++ show i)) [1 .. length pats]
	let drhs = untypedAbs dvars $ sep (text "f" : dvars)
	dclauses <- mapM showUntypedClause clauses
	return $ (dname <+> equals) <+> drhs <+> text "where" $+$
		 nest 2 (vcat dclauses)
      Datatype np ni _ cnames s a -> do
	let dvars = map (\i -> text ("v" ++ show i)) [1 .. np + ni]
	let drhs = untypedAbs dvars $ text "VNonData"
	return $ sep [ dname, equals ] <+> drhs <+> text "{- datatype -}"
      Record np clauses flds tel s a -> do
        dcname <- showAsUntypedConstructor name
	let arity = length flds
	let dvars = map (\i -> text ("v" ++ show i)) [1 .. arity]
	let drhs = untypedAbs dvars $ sep $
		   text "VCon" <> text (show arity) : dcname : dvars
	return $ sep [ dname, equals ] <+> drhs
      Constructor np _ qtname a -> do
	dcname <- showAsUntypedConstructor name
	ty <- instantiate $ defType defn
	(args,_) <- splitType ty
	let arity = length args - np
	let dvars = map (\i -> text ("v" ++ show i)) [1 .. arity]
	let drhs = untypedAbs dvars $ sep $
		   text "VCon" <> text (show arity) : dcname : dvars
	return $ sep [ dname, equals ] <+> drhs
      Primitive a pf _ -> do
	doptname <- showAsOptimizedTerm name
	return $ sep [ dname, equals ] <+>
		 sep [ text "box", doptname, text "{- primitive -}" ]

untypedAbs :: [Doc] -> Doc -> Doc
untypedAbs dvars dtail = foldr
    (\dvar d -> sep [ text "VAbs (\\" <> dvar <+> text "->",
		      d <> text ")" ]) dtail dvars

----------------------------------------------------------------

underUntypedClauseBody :: ClauseBody -> ([Doc] -> Term -> TCM Doc) -> TCM Doc
underUntypedClauseBody body k = go 0 [] body where
    go n dvars NoBody        = return empty
    go n dvars (Body t)      = k dvars t
    go n dvars (NoBind body) = go n (dvars ++ [text "_"]) body
    go n dvars (Bind abs)    =
	underAbstraction_ abs{absName = show (n + 1)} $ \body -> do
	    dvar <- showAsUntypedTerm $ Var 0 []
	    go (n + 1) (dvars ++ [dvar]) body

showUntypedClause :: Clause -> TCM Doc
showUntypedClause (Clause pats NoBody) = return empty
showUntypedClause (Clause pats body)   = underUntypedClauseBody body $
    \dvars term -> do
	(_,dpats) <- showUntypedPatterns dvars $ map unArg pats
	dbody <- showAsUntypedTerm term
	return $ text "f" <+> sep [ sep [ sep dpats, equals ], dbody ]

showUntypedPatterns :: [Doc] -> [Pattern] -> TCM ([Doc], [Doc])
showUntypedPatterns dvars []           = return (dvars,[])
showUntypedPatterns dvars (pat : pats) = do
    (dvars', dpat)  <- showUntypedPattern  dvars  pat
    (dvars'',dpats) <- showUntypedPatterns dvars' pats
    return (dvars'', (dpat : dpats))

showUntypedPattern :: [Doc] -> Pattern -> TCM ([Doc], Doc)
showUntypedPattern (dvar : dvars) (VarP s) = return (dvars, dvar)
showUntypedPattern []             (VarP s) = return __IMPOSSIBLE__
showUntypedPattern dvars (ConP qname args) = do
    dname <- showAsUntypedConstructor qname
    (dvars',dargs) <- showUntypedPatterns dvars (map unArg args)
    return (dvars', parens $ (text "VCon" <> text (show (length dargs))) <+>
			 sep (dname : dargs))
showUntypedPattern dvars (LitP lit) =
    return (dvars, parens $ showUntypedLiteral lit)

----------------------------------------------------------------
--

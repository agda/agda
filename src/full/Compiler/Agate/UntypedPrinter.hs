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

showQNameAsUntypedConstructor :: QName -> TCM Doc
showQNameAsUntypedConstructor qname =
    return $ text $ translateNameAsUntypedConstructor $ show qname

----------------------------------------------------------------
-- implementation of the "X" function

class ShowAsUntypedTerm a where
    showAsUntypedTerm :: a -> TCM Doc 

instance ShowAsUntypedTerm Name where
    showAsUntypedTerm t = return $ text $ translateNameAsUntypedTerm $ show t

instance ShowAsUntypedTerm QName where
    showAsUntypedTerm t = return $ text $ translateNameAsUntypedTerm $ show t

instance ShowAsUntypedTerm Term where
    showAsUntypedTerm (Var n args) =
     do varname <- nameOfBV n
    	dvar <- showAsUntypedTerm varname
    	dargs <- mapM showAsUntypedTerm (map unArg args)
        return $ foldl (\f a -> parens (f <+> text "|$|" <+> a)) dvar dargs
    showAsUntypedTerm (Lam h abs@(Abs v b)) =
     do newname <- freshName_ (absName abs)
	addCtx newname __IMPOSSIBLE__ $ do
	    dvar <- showAsUntypedTerm $ Var 0 []
	    dbody <- showAsUntypedTerm (absBody abs)
	    return $ parens $ text "VAbs" <+>
		     parens (sep [ text "\\" <> dvar, text "->", dbody ])
    showAsUntypedTerm (Con qname args) =
     do dname <- showAsUntypedTerm qname
    	dargs <- mapM showAsUntypedTerm (map unArg args)
        return $ foldl (\f a -> parens (f <+> text "|$|" <+> a)) dname dargs
    showAsUntypedTerm (Def qname args) =
     do dname <- showAsUntypedTerm qname
    	dargs <- mapM showAsUntypedTerm (map unArg args)
        return $ foldl (\f a -> parens (f <+> text "|$|" <+> a)) dname dargs
    showAsUntypedTerm (Lit (LitInt    _ i)) = return $ parens $ text "VInt" <+> text (show i)
    showAsUntypedTerm (Lit (LitString _ s)) = return $ parens $ text "VString" <+> text (show s)
    showAsUntypedTerm (Lit (LitFloat  _ f)) = return $ parens $ text "VFloat" <+> text (show f)
    showAsUntypedTerm (Lit (LitChar   _ c)) = return $ parens $ text "VChar" <+> text (show c)
    showAsUntypedTerm (Pi _ _)	   = __IMPOSSIBLE__ -- not impossible
    showAsUntypedTerm (Fun _ _)    = __IMPOSSIBLE__ -- not impossible
    showAsUntypedTerm (Sort _)	   = __IMPOSSIBLE__ -- not impossible
    showAsUntypedTerm (MetaV _ _)  = __IMPOSSIBLE__
    showAsUntypedTerm (BlockedV _) = __IMPOSSIBLE__

instance ShowAsUntypedTerm ClauseBody where
    showAsUntypedTerm (Body t)      = showAsUntypedTerm t
    showAsUntypedTerm (Bind abs)    = do
	newname <- freshName_ (absName abs)
	addCtx newname __IMPOSSIBLE__ $ showAsUntypedTerm (absBody abs)
    showAsUntypedTerm (NoBind body) = showAsUntypedTerm body
    showAsUntypedTerm NoBody        = return $ text "error \"impossible\""

----------------------------------------------------------------

class ShowAsUntyped a where
    showAsUntyped :: a -> TCM Doc 

instance ShowAsUntyped Pattern where
    showAsUntyped (VarP s)          =
	return $ text $ translateNameAsUntypedTerm s
    showAsUntyped (ConP qname args) = do
	dname <- showQNameAsUntypedConstructor qname
	dargs <- mapM (showAsUntyped . unArg) args
	return $ parens $ (text "VCon" <> text (show (length dargs))) <+>
			  sep (dname : dargs)
    showAsUntyped (LitP lit) = return $ text (show lit)

showClause :: Clause -> TCM Doc
showClause (Clause pats NoBody) = return empty
showClause (Clause pats body)   = do
    dpats <- mapM (showAsUntyped . unArg) pats 
    dbody <- showAsUntypedTerm body
    return $ text "f" <+>
	     sep [ sep [ sep dpats, equals ], dbody ]

----------------------------------------------------------------

showNDefinition :: (QName, Definition) -> TCM Doc
showNDefinition (name, defn) = do
    dname <- showAsUntypedTerm name
    case theDef defn of
      Axiom -> do
	return $ sep [ dname, equals ] <+>
		 sep [ text "undefined {- postulate -}" ]
      Function [] a -> return $ text "return __IMPOSSIBLE__"
      Function clauses a -> do
        let (Clause pats body) = head clauses
	let patsize = length pats
	let dvars = map (\i -> text ("v" ++ show i)) [1..patsize]
	let drhs = untypedAbs dvars $ sep (text "f" : dvars)
	dclauses <- mapM showClause clauses
	return $ (dname <+> equals) <+> drhs <+> text "where" $+$
		 nest 2 (vcat dclauses)
      Datatype np ni _ qcnames s a -> do
	ty <- instantiate $ defType defn
	(args,_) <- splitType ty
	let dvars = map (\i -> text ("v" ++ show i)) [1 .. np + ni]
	let drhs = untypedAbs dvars $ text "VNonData"
	return $ sep [ dname, equals ] <+> drhs <+> text "{- datatype -}"
      Record _ _ _ _ _ _ -> return $ text "(error \"records\")"
      Constructor np _ qtname a -> do
	dcname <- showAsUntypedConstructor name
	ty <- instantiate $ defType defn
	(args,_) <- splitType ty
	let argsize = length args
	let dvars = map (\i -> text ("v" ++ show i)) [1..argsize]
	let dargvars = drop np dvars
	let drhs = untypedAbs dvars $ sep $
		    text "VCon" <> text (show (argsize - np)) : dcname : dargvars
	return $ sep [ dname, equals ] <+> drhs
      Primitive a pf _ -> do
	doname <- showAsOptimizedTerm name
	return $ sep [ dname, equals ] <+>
		 sep [ text "box", doname, text "{- primitive -}" ]

untypedAbs :: [Doc] -> Doc -> Doc
untypedAbs dvars dtail = foldr
    (\dvar d -> sep [ text "VAbs (\\" <> dvar <+> text "->",
		      d <> text ")" ]) dtail dvars

----------------------------------------------------------------
--

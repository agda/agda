{-# OPTIONS -fglasgow-exts -cpp #-}

#include "../../undefined.h"

{-| Generate GHC code for optimized datatypes and their values
-}

module Compiler.Agate.OptimizedPrinter where

import Control.Monad.Trans
import qualified Data.Map as Map
import Data.Map ((!), Map)

import Compiler.Agate.Classify
import Compiler.Agate.TranslateName
import Compiler.Agate.Common

import Syntax.Common
import Syntax.Internal
import TypeChecking.Monad
import TypeChecking.Reduce
import TypeChecking.Free
import Utils.Pretty

----------------------------------------------------------------

showQNameAsOptimizedConstructor :: QName -> TCM Doc
showQNameAsOptimizedConstructor s =
    return $ text $ translateNameAsOptimizedConstructor $ show s
    
showNameAsOptimizedConstructor :: QName -> TCM Doc
showNameAsOptimizedConstructor s =
    return $ text $ translateNameAsOptimizedConstructor $ show s

----------------------------------------------------------------

showOptimizedDefinitions :: Definitions -> TCM ()
showOptimizedDefinitions definitions = do
    liftIO $ putStrLn ("\n-----\n")
    let allDatatypes = enumDatatypes definitions
    compilableDatatypes <- enumCompilableDatatypes definitions allDatatypes
    dtypedecls <- showTypeDeclarations definitions compilableDatatypes
    liftIO $ putStrLn $ render dtypedecls
    optimizableConstants <- enumOptimizableConstants definitions compilableDatatypes
    liftIO $ putStrLn $ ""
    dvaluedefs <- showValueDefinitions definitions compilableDatatypes
    liftIO $ putStrLn $ render dvaluedefs
    return ()

----------------------------------------------------------------
-- Generating GHC Type Declarations

showTypeDeclarations :: Definitions -> [QName] -> TCM Doc
showTypeDeclarations definitions compilableDatatypes = do
    dtypedecls <- mapM (showTypeDeclaration definitions) compilableDatatypes
    return $ vcat dtypedecls

showTypeDeclaration :: Definitions -> QName -> TCM Doc
showTypeDeclaration definitions name = do
    let defn = definitions ! name
    let (Datatype np ni _ qcnames s a) = theDef defn
    ty <- instantiate $ defType defn
    underContext ty $ do
    	dtypename <- showAsOptimizedType name
    	dparams <- mapM showTypeParameter $ reverse [0 .. np + ni - 1]
    	dargs <- mapM (showConstructorDeclaration definitions np) qcnames
    	case dargs of
	    []  -> return $ (text "type") <+> (
				sep (dtypename : dparams) <+> equals <+>
				text "()")
	    _:_ -> return $ (text "data") <+> (sep $
				sep (dtypename : dparams) <+> equals :
				punctuate (text " |") dargs)
			    $+$ text "    -- deriving (Show)"

showTypeParameter :: Nat -> TCM Doc
showTypeParameter n = do
    dname <- showAsOptimizedTerm $ Var n []
    ty <- typeOfBV n
    ty <- instantiate ty
    (args,_) <- splitType ty
    case args of
	[]  -> return dname
	_:_ -> do
		dk <- showAsOptimizedKind ty
		return $ parens $ sep [ dname <+> text "::", dk ]

showConstructorDeclaration :: Definitions -> Int -> QName -> TCM Doc
showConstructorDeclaration definitions np qcname = do
    dcon <- showNameAsOptimizedConstructor qcname
    let defn = definitions ! qcname
    ty <- instantiate $ defType defn
    ty <- dropArgs np ty
    dargs <- forEachArgM showAsOptimizedType ty
    return $ sep $ dcon : dargs


----------------------------------------------------------------
-- Generating GHC Value Definitions

showValueDefinitions :: Definitions -> [QName] -> TCM Doc
showValueDefinitions definitions compilableDatatypes = do
    let defs = Map.toList definitions
    dvaluedefs <- mapM (showValueDefinition definitions compilableDatatypes) defs
    return $ vcat dvaluedefs

showValueDefinition :: Definitions -> [QName] -> (QName,Definition) -> TCM Doc
showValueDefinition definitions compilableDatatypes (name,defn) = do
    dname <- showAsOptimizedTerm name
    ddef  <- case theDef defn of
      Axiom -> do
	return $ sep [ dname, equals ] <+>
		 sep [ text "undefined {- postulate -}" ]
      Function clauses a -> do
	dclauses <- mapM (showClauseAsOptimized name) clauses
	return $ vcat dclauses
      Datatype np ni _ qcnames s a -> do
	ty <- instantiate $ defType defn
	underContext ty $ do
    		dparams <- mapM (showAsOptimizedTerm. flip Var [])
    			$ reverse [0..(np - 1)]
		return $ sep [ sep (dname : dparams), equals ] <+>
			 text "()"
      Record _ _ _ _ _ _ -> return $ text "(error \"records\")"
      Constructor np _ qtname a -> do
	dcname <- showNameAsOptimizedConstructor name
	let dparams = map (const $ text "_") [0..(np - 1)]
	return $ sep [ sep (dname : dparams), equals ] <+> dcname
      Primitive a pf _ -> do
	doptname <- showAsOptimizedTerm name
	return $ sep [ dname, equals ] <+>
		 sep [ text (show name), text "{- primitive -}" ]
    ty <- instantiate $ defType defn
    dty <- showAsOptimizedType ty
    let dtype = sep [ dname, text "::" ] <+> dty
    return $ dtype $+$ ddef		


showClauseAsOptimized :: QName -> Clause -> TCM Doc
showClauseAsOptimized name (Clause pats NoBody) = return empty
showClauseAsOptimized name (Clause pats body)   = do
    dname <- showAsOptimizedTerm name
    dpats <- mapM (showAsOptimized . unArg) pats 
    dbody <- showAsOptimizedTerm body
    return $ dname <+> sep [ sep dpats <+> text "=", dbody ]

----------------------------------------------------------------
-- implementation of the "K" function

class ShowAsOptimizedKind a where
    showAsOptimizedKind :: a -> TCM Doc 

instance ShowAsOptimizedKind Type where
    showAsOptimizedKind (El s t) = showAsOptimizedKind t

instance ShowAsOptimizedKind Term where
    showAsOptimizedKind t = do
	t <- reduce t
	case ignoreBlocking t of
	    Pi arg abs -> do
		dk1 <- showAsOptimizedKind $ unArg arg
		dk2 <- showAsOptimizedKind $ absBody abs
		return $ parens $ sep [dk1 <+> text "->", dk2]
	    Fun arg ty -> do
		dk1 <- showAsOptimizedKind $ unArg arg
		dk2 <- showAsOptimizedKind $ ty
		return $ parens $ sep [dk1 <+> text "->", dk2]
	    Sort s     -> return $ text "*"
	    Var _ _    -> return $ text "<var (impossible)>"
	    Def _ _    -> __IMPOSSIBLE__
	    Con _ _    -> __IMPOSSIBLE__
	    Lit _      -> __IMPOSSIBLE__
	    MetaV _ _  -> __IMPOSSIBLE__
	    Lam _ _    -> __IMPOSSIBLE__
	    BlockedV _ -> __IMPOSSIBLE__

----------------------------------------------------------------
-- implementation of the "T" function

class ShowAsOptimizedType a where
    showAsOptimizedType :: a -> TCM Doc 

instance ShowAsOptimizedType QName where
    showAsOptimizedType s = return $ text $ translateNameAsOptimizedType $ show s

instance ShowAsOptimizedType Type where
    showAsOptimizedType (El s t) = showAsOptimizedType t

instance ShowAsOptimizedType Term where
    showAsOptimizedType t = do
	t <- reduce t
	case ignoreBlocking t of
	    Var n args -> do
		varname <- nameOfBV n
		dvar <- showAsOptimizedTerm varname
		dargs <- mapM (showAsOptimizedType . unArg) args
		return $ psep $ dvar : dargs
	    Def qname args -> do
		dname <- showAsOptimizedType qname
		dargs <- mapM (showAsOptimizedType . unArg) args
		return $ psep $ dname : dargs
	    Con name args -> do
		return $ text "<constructor term (impossible)>"
	    Pi arg abs -> do
		dt1 <- showAsOptimizedType $ unArg arg
		newname <- freshName_ $ absName abs
		addCtx newname arg $ do
		    dvar <- showAsOptimizedTerm $ Var 0 []
		    dt2 <- showAsOptimizedType $ absBody abs
		    case freeIn 0 $ absBody abs of
			True  -> return $ parens $ sep $
			    [ sep [ text "forall",
				    dvar <> text ".", dt1, text "->" ],
			      dt2 ]
			False -> return $ parens $ sep [dt1 <+> text "->", dt2]
	    Fun arg ty -> do
		dt1 <- showAsOptimizedType $ unArg arg
		dt2 <- showAsOptimizedType $ ty
		return $ parens $ sep [dt1, text "->", dt2]
	    Sort s        -> return $ text "()"
	    MetaV id args -> return $ text "<meta (impossible)>"
	    Lam h t       -> __IMPOSSIBLE__
	    Lit lit       -> __IMPOSSIBLE__
	    BlockedV bt   -> __IMPOSSIBLE__


----------------------------------------------------------------
-- implementation of the "O" function

class ShowAsOptimizedTerm a where
    showAsOptimizedTerm :: a -> TCM Doc 

instance ShowAsOptimizedTerm Name where
    showAsOptimizedTerm s = return $ text $ translateNameAsOptimizedTerm $ show s

instance ShowAsOptimizedTerm QName where
    showAsOptimizedTerm s = return $ text $ translateNameAsOptimizedTerm $ show s

instance ShowAsOptimizedTerm Term where
    showAsOptimizedTerm (Var n args)     = do
    	varname <- nameOfBV n
    	dvar <- showAsOptimizedTerm varname
    	dargs <- mapM (showAsOptimizedTerm . unArg) args
    	return $ psep $ dvar : dargs
    showAsOptimizedTerm (Lam h abs)      = do
    	newname <- freshName_ $ absName abs
    	addCtx newname __IMPOSSIBLE__ $ do
    	    dvar <- showAsOptimizedTerm $ Var 0 []
    	    dt <- showAsOptimizedTerm $ absBody abs
    	    return $ parens $ sep [ text "\\" <> dvar, text "->", dt ]
    showAsOptimizedTerm (Lit lit) = return $ text $ showLiteralContent lit
    showAsOptimizedTerm (Def qname args) = do
	let name = qnameName qname
	dname <- showAsOptimizedTerm name
	dargs <- mapM (showAsOptimizedTerm . unArg) args
	return $ psep $ dname : dargs
    showAsOptimizedTerm (Con qname args) = do
    	let name = qnameName qname
    	dname <- showAsOptimizedTerm name
    	dargs <- mapM (showAsOptimizedTerm . unArg) args
    	return $ psep $ dname : dargs
    showAsOptimizedTerm (Pi _ _)	 = return $ text "()"
    showAsOptimizedTerm (Fun _ _)	 = return $ text "()"
    showAsOptimizedTerm (Sort _)	 = return $ text "()"
    showAsOptimizedTerm (MetaV id args)  = __IMPOSSIBLE__
    showAsOptimizedTerm (BlockedV bt)    = __IMPOSSIBLE__


instance ShowAsOptimizedTerm ClauseBody where
    showAsOptimizedTerm (Body t)      = showAsOptimizedTerm t
    showAsOptimizedTerm (Bind abs)    = do
	newname <- freshName_ (absName abs)
	addCtx newname __IMPOSSIBLE__ $ showAsOptimizedTerm (absBody abs)
    showAsOptimizedTerm (NoBind body) = showAsOptimizedTerm body
    showAsOptimizedTerm NoBody        = return $ text "error \"impossible\""

----------------------------------------------------------------

class ShowAsOptimized a where
    showAsOptimized :: a -> TCM Doc 

instance ShowAsOptimized Pattern where
    showAsOptimized (VarP s) =
	return $ text $ translateNameAsOptimizedTerm s
    showAsOptimized (ConP qname args) = do
	dname <- showQNameAsOptimizedConstructor qname
	dargs <- mapM (showAsOptimized . unArg) args
	return $ parens $ sep $ dname : dargs
    showAsOptimized (LitP lit) = return $ text $ show lit

----------------------------------------------------------------

--

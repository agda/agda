{-# OPTIONS -fglasgow-exts -cpp #-}

#include "../../undefined.h"

{-| Generate GHC code for optimized datatypes and their values
-}

module Compiler.Agate.OptimizedPrinter where

import Control.Monad.Trans
import qualified Data.Map as Map
import Data.Map ((!))

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
    return $ text $ translateNameAsOptimizedConstructor s
    
showNameAsOptimizedConstructor :: Name -> TCM Doc
showNameAsOptimizedConstructor s =
    return $ text $ translateNameAsOptimizedConstructor s
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

showTypeDeclarations :: Definitions -> [Name] -> TCM Doc
showTypeDeclarations definitions compilableDatatypes = do
    dtypedecls <- mapM (showTypeDeclaration definitions) compilableDatatypes
    return $ vcat dtypedecls

showTypeDeclaration :: Definitions -> Name -> TCM Doc
showTypeDeclaration definitions name = do
    let defn = definitions ! name
    let (Datatype np qcnames s a) = theDef defn
    ty <- instantiate $ defType defn
    underContext ty $ do
    	dtypename <- showAsOptimizedType name
    	dparams <- mapM showTypeParameter $ reverse [0..(np - 1)]
    	dargs <- mapM (showConstructorDeclaration definitions np) qcnames
    	case dargs of
	    []  -> return $ (text "type") <+> (
				sep (dtypename : dparams) <+> equals <+>
				text "()")
	    _:_ -> return $ (text "data") <+> (sep $
				sep (dtypename : dparams) <+> equals :
				punctuate (text " |") dargs)

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
    let con = qnameName qcname
    dcon <- showNameAsOptimizedConstructor con -- qcname
    let defn = definitions ! con
    ty <- instantiate $ defType defn
    ty <- dropArgs np ty
    dargs <- forEachArgM showAsOptimizedType ty
    return $ sep $ dcon : dargs


----------------------------------------------------------------
-- Generating GHC Value Definitions

showValueDefinitions :: Definitions -> [Name] -> TCM Doc
showValueDefinitions definitions compilableDatatypes = do
    let defs = Map.toList definitions
    dvaluedefs <- mapM (showValueDefinition definitions compilableDatatypes) defs
    return $ vcat dvaluedefs

showValueDefinition :: Definitions -> [Name] -> (Name,Definition) -> TCM Doc
showValueDefinition definitions compilableDatatypes (name,defn) = do
    dname <- showAsOptimizedTerm name
    ddef  <- case theDef defn of
      Axiom -> do
	return $ sep [ dname, equals ] <+>
		 sep [ text "undefined {- postulate -}" ]
      Function clauses a -> do
	dclauses <- mapM (showClauseAsOptimized name) clauses
	return $ vcat dclauses
      Datatype np qcnames s a -> do
	ty <- instantiate $ defType defn
	underContext ty $ do
    		dparams <- mapM (showAsOptimizedTerm. flip Var [])
    			$ reverse [0..(np - 1)]
		return $ sep [ sep (dname : dparams), equals ] <+>
			 text "()"
      Constructor np qtname a -> do
	dcname <- showNameAsOptimizedConstructor name
	let dparams = map (const $ text "_") [0..(np - 1)]
	return $ sep [ sep (dname : dparams), equals ] <+> dcname
      Primitive a pf -> do
	doptname <- showAsOptimizedTerm name
	return $ sep [ dname, equals ] <+>
		 sep [ text (show name), text "{- primitive -}" ]
    ty <- instantiate $ defType defn
    dty <- showAsOptimizedType ty
    let dtype = sep [ dname, text "::" ] <+> dty
    return $ dtype $+$ ddef		


showClauseAsOptimized :: Name -> Clause -> TCM Doc
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
    showAsOptimizedKind (El t s) = return $ text "*" -- assumes Pi not in Set
    showAsOptimizedKind (Pi arg abs) = do
    	dk1 <- showAsOptimizedKind $ unArg arg
	dk2 <- showAsOptimizedKind $ absBody abs
	return $ parens $ sep [dk1, text "->", dk2]
    showAsOptimizedKind (Fun arg ty) = do
	dk1 <- showAsOptimizedKind $ unArg arg
	dk2 <- showAsOptimizedKind $ ty
	return $ parens $ sep [dk1, text "->", dk2]
    showAsOptimizedKind (Sort s)        = return $ text "*"
    showAsOptimizedKind (MetaT id args) = return __IMPOSSIBLE__
    showAsOptimizedKind (LamT abs)      = return __IMPOSSIBLE__

----------------------------------------------------------------
-- implementation of the "T" function

class ShowAsOptimizedType a where
    showAsOptimizedType :: a -> TCM Doc 

instance ShowAsOptimizedType Name where
    showAsOptimizedType s = return $ text $ translateNameAsOptimizedType s

instance ShowAsOptimizedType Term where
    showAsOptimizedType (Var n args)   = do
    	varname <- nameOfBV n
    	dvar <- showAsOptimizedTerm varname
    	dargs <- mapM (showAsOptimizedType . unArg) args
    	return $ psep $ dvar : dargs
    showAsOptimizedType (Lam h t)        = __IMPOSSIBLE__
    showAsOptimizedType (Lit literal)    = __IMPOSSIBLE__
    showAsOptimizedType (Def qname args) = do
	let name = qnameName qname
	dname <- showAsOptimizedType name
	dargs <- mapM (showAsOptimizedType . unArg) args
	return $ psep $ dname : dargs
    showAsOptimizedType (Con name args) =
	return $ text "<constructor term (impossible)>"
    showAsOptimizedType (MetaV id args) = return $ text "<meta (impossible)>"
    showAsOptimizedType (BlockedV bt)   = __IMPOSSIBLE__

instance ShowAsOptimizedType Type where
    showAsOptimizedType (El t s) = showAsOptimizedType t
    showAsOptimizedType (Pi arg abs) = do
    	dt1 <- showAsOptimizedType $ unArg arg
	newname <- freshName_ $ absName abs
    	addCtx newname (unArg arg) $ do
    	    dvar <- showAsOptimizedTerm $ Var 0 []
	    dt2 <- showAsOptimizedType $ absBody abs
	    case freeIn 0 $ absBody abs of
		True  -> return $ parens $ sep $
		    [ sep [ text "forall", dvar <> text ".", dt1, text "->" ],
		      dt2 ]
		False -> return $ parens $ sep [ dt1 <+> text "->", dt2 ]
    showAsOptimizedType (Fun arg ty) = do
	dt1 <- showAsOptimizedType $ unArg arg
	dt2 <- showAsOptimizedType $ ty
	return $ parens $ sep [dt1, text "->", dt2]
    showAsOptimizedType (Sort s)        = return $ text "()"
    showAsOptimizedType (MetaT id args) = return $ text "<META (impossible)>"
    showAsOptimizedType (LamT abs)      = return __IMPOSSIBLE__

----------------------------------------------------------------
-- implementation of the "O" function

class ShowAsOptimizedTerm a where
    showAsOptimizedTerm :: a -> TCM Doc 

instance ShowAsOptimizedTerm Name where
    showAsOptimizedTerm s = return $ text $ translateNameAsOptimizedTerm s

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
    showAsOptimizedTerm (MetaV id args)  = __IMPOSSIBLE__
    showAsOptimizedTerm (BlockedV bt)    = __IMPOSSIBLE__


instance ShowAsOptimizedTerm ClauseBody where
    showAsOptimizedTerm (Body t)      = showAsOptimizedTerm t
    showAsOptimizedTerm (Bind abs)    = do
	newname <- freshName_ (absName abs)
	addCtx newname __IMPOSSIBLE__ $ showAsOptimizedTerm (absBody abs)
    showAsOptimizedTerm (NoBind body) = showAsOptimizedTerm body
    showAsOptimizedTerm NoBody        = return $ text "(absurd)"

----------------------------------------------------------------

class ShowAsOptimized a where
    showAsOptimized :: a -> TCM Doc 

instance ShowAsOptimized Pattern where
    showAsOptimized (VarP s) =
	return $ text $ translateNameAsOptimizedTerm (VarP s)
    showAsOptimized (ConP qname args) = do
	dname <- showQNameAsOptimizedConstructor qname
	dargs <- mapM (showAsOptimized . unArg) args
	return $ parens $ sep $ dname : dargs
    showAsOptimized (LitP lit) = return $ text $ show lit
    showAsOptimized AbsurdP    = return $ text "()" -- __IMPOSSIBLE__

----------------------------------------------------------------

--

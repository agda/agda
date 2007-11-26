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
import Utils.Size

----------------------------------------------------------------

showAsOptimizedConstructor :: QName -> TCM Doc
showAsOptimizedConstructor s =
    return $ text $ translateNameAsOptimizedConstructor $ show s

----------------------------------------------------------------

showOptimizedDefinitions :: Definitions -> TCM ()
showOptimizedDefinitions definitions = do
    liftIO $ putStrLn ("\n-----\n")
    typefams <- enumCompilableTypeFamilies definitions
    dtypedecls <- showTypeDeclarations definitions typefams
    liftIO $ putStrLn $ render dtypedecls
    optimizableConstants <- enumOptimizableConstants definitions typefams
    liftIO $ putStrLn $ ""
    dvaluedefs <- showValueDefinitions definitions typefams
    liftIO $ putStrLn $ render dvaluedefs
    return ()

----------------------------------------------------------------
-- Generating GHC Type Declarations

showTypeDeclarations :: Definitions -> [QName] -> TCM Doc
showTypeDeclarations definitions typefams = do
    dtypedecls <- mapM (showTypeDeclaration definitions) typefams
    return $ vcat dtypedecls

showTypeDeclaration :: Definitions -> QName -> TCM Doc
showTypeDeclaration definitions name = do
    dtypename <- showAsOptimizedType name
    let defn = definitions ! name
    ty <- normalise $ defType defn
    case theDef defn of
	Datatype np ni _ cnames s a | ni == 0 -> do
	    dparams <- underDatatypeParameters np ty showTypeParameter stop
	    dargs <- mapM (showConstructorDeclaration np) cnames
	    showDatatypeDeclaration dtypename dparams dargs
	Record np clauses flds tel s a -> do
	    let arity = np `div` 2
	    dparams <- underDatatypeParameters arity ty showTypeParameter stop
	    dcon <- showAsOptimizedConstructor name
	    dflds <- mapM (showRecordFieldDeclaration (arity + 1)) flds
	    showDatatypeDeclaration dtypename dparams [sep $ dcon : dflds]
     	Function [clause@(Clause _ _ pat body)] a -> do
	    (args,_) <- splitType ty
	    let dextra = map (\i -> text $ "a" ++ show i)
			     [length pat + 1 .. length args]
	    showTypeSynonymDeclaration dtypename dextra clause
     	_ -> return empty
    where
    stop ty = return []
    showDatatypeDeclaration dtypename dparams [] =
	return $ (text "type") <+> (sep (dtypename : dparams) <+> equals <+>
				    text "()")
    showDatatypeDeclaration dtypename dparams dargs =
	return $ (text "data") <+> (sep $
				    sep (dtypename : dparams) <+> equals :
				    punctuate (text " |") dargs)
				$+$ text "    -- deriving (Show)"
    showTypeSynonymDeclaration dtypename dextra = showClause fTerm fCon fBody
	where
	fTerm = showAsOptimizedType
	fCon name dargs = __IMPOSSIBLE__
	fBody dpats term = do
	    dterm <- showAsOptimizedType term
	    return $ (text "type") <+>
		     (sep (dtypename : (dpats ++ dextra)) <+> equals <+>
		      sep (dterm : dextra))

    showConstructorDeclaration np cname = do
	let defn = definitions ! cname
	ty <- normalise $ defType defn
	dcon <- showAsOptimizedConstructor cname
	underDatatypeParameters np ty (\d t -> return id) $ \ty -> do
	    dargs <- forEachArgM showAsOptimizedType ty
	    return $ sep $ dcon : dargs
    showRecordFieldDeclaration np fldname = do
	let defn = definitions ! fldname
	ty <- normalise $ defType defn
	underDatatypeParameters np ty (\d t -> return id) showAsOptimizedType

showTypeParameter :: Doc -> Type -> TCM ([Doc] -> [Doc])
showTypeParameter dname ty = do
    ty <- instantiate ty
    (args,_) <- splitType ty
    case args of
	[]  -> return $ (:) dname
	_:_ -> do
		dk <- showAsOptimizedKind ty
		return $ (:) $ parens $ sep [ dname <+> text "::", dk ]

underDatatypeParameters :: Int -> Type -> (Doc -> Type -> TCM (a -> a)) ->
			   (Type -> TCM a) -> TCM a
underDatatypeParameters np ty f k = go 0 ty where
    go i ty        | i >= np = k ty
    go i (El s tm)           = do
      let varname = show (i + 1)
      tm <- reduce tm
      case ignoreBlocking tm of
	Pi arg abs -> underAbstraction arg abs{absName = varname} $ \ty -> do
	    dname <- showAsOptimizedTerm $ Var 0 []
	    cont <- f dname $ unArg arg
	    dparams <- go (i + 1) ty
	    return $ cont dparams
	Fun arg ty -> do
	    let dname = text $ translateNameAsOptimizedTerm varname
	    cont <- f dname $ unArg arg
	    dparams <- go (i + 1) ty
	    return $ cont dparams
	Var _ _    -> __IMPOSSIBLE__
	Def _ _    -> __IMPOSSIBLE__
	Con _ _    -> __IMPOSSIBLE__
	Sort _	   -> __IMPOSSIBLE__
	Lit _	   -> __IMPOSSIBLE__
	MetaV _ _  -> __IMPOSSIBLE__
	Lam _ _	   -> __IMPOSSIBLE__
	BlockedV _ -> __IMPOSSIBLE__

----------------------------------------------------------------
-- Generating GHC Value Definitions

showValueDefinitions :: Definitions -> [QName] -> TCM Doc
showValueDefinitions definitions typefams = do
    let defs = Map.toList definitions
    dvaluedefs <- mapM (showValueDefinition definitions typefams) defs
    return $ vcat dvaluedefs

showValueDefinition :: Definitions -> [QName] -> (QName,Definition) -> TCM Doc
showValueDefinition definitions typefams (name, defn) = do
    dname <- showAsOptimizedTerm name
    ty <- normalise $ defType defn
    dty <- showAsOptimizedType ty
    let dtypedecl = sep [ dname, text "::" ] <+> dty
    case theDef defn of
	Axiom -> do
	    let dvaluedef = sep [ dname, equals ] <+>
			    sep [ text "undefined {- postulate -}" ]
	    return $ dtypedecl $+$ dvaluedef
	Function clauses a -> do
	    dclauses <- mapM (showOptimizedClause dname) clauses
	    return $ vcat $ dtypedecl : dclauses
	Datatype np ni _ cnames s a -> do
	    let dvars = map (\i -> text ("v" ++ show i)) [1 .. np + ni]
	    let dvaluedef = sep [ sep (dname : dvars), equals ] <+> text "()"
	    return $ dtypedecl $+$ dvaluedef
	Record np clauses flds tel s a -> 
	    return empty  -- no o_xxx since we always use D_xxx
	Constructor np _ tname a ->
	    return empty  -- no o_xxx since we always use D_xxx
	Primitive a pf _ -> do
	    let dvaluedef = sep [ dname, equals ] <+>
			    sep [ text (show name), text "{- primitive -}" ]
	    return $ dtypedecl $+$ dvaluedef

showOptimizedClause :: Doc -> Clause -> TCM Doc
showOptimizedClause dfuncname = showClause fTerm fCon fBody where
    fTerm = showAsOptimizedTerm
    fCon name dargs = do
	dname <- showAsOptimizedConstructor name
	return $ parens $ sep (dname : dargs)    
    fBody dpats term = do
	dterm <- showAsOptimizedTerm term
	return $ (sep (dfuncname : dpats) <+> equals) <+> nest 2 dterm

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
	    Var _ _    -> return $ text "*" -- ok?
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
	    Def name args -> do
		dname <- showAsOptimizedType name
		dargs <- mapM (showAsOptimizedType . unArg) args
		return $ psep $ dname : dargs
	    Con name args -> do
		return $ text "<constructor term (impossible)>"
	    Pi arg abs -> do
		dt1 <- showAsOptimizedType $ unArg arg
		underAbstraction_ abs $ \body -> do
		    dvar <- showAsOptimizedTerm $ Var 0 []
		    dt2 <- showAsOptimizedType body
		    case freeIn 0 body of
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
    showAsOptimizedTerm (Var n args) = do
    	varname <- nameOfBV n
    	dvar <- showAsOptimizedTerm varname
    	dargs <- mapM (showAsOptimizedTerm . unArg) args
    	return $ psep $ dvar : dargs
    showAsOptimizedTerm (Lam h abs) = underAbstraction_ abs $ \body -> do
    	dvar <- showAsOptimizedTerm $ Var 0 []
    	dt <- showAsOptimizedTerm body
    	return $ parens $ sep [ text "\\" <> dvar, text "->", dt ]
    showAsOptimizedTerm (Def name args) = do
	dname <- showAsOptimizedTerm name
	dargs <- mapM (showAsOptimizedTerm . unArg) args
	return $ psep $ dname : dargs
    showAsOptimizedTerm (Con name args) = do
    	dname <- showAsOptimizedConstructor name
    	dargs <- mapM (showAsOptimizedTerm . unArg) args
    	return $ psep $ dname : dargs
    showAsOptimizedTerm (Lit lit)        = return $ showOptimizedLiteral lit
    showAsOptimizedTerm (Pi _ _)	 = return $ text "()"
    showAsOptimizedTerm (Fun _ _)	 = return $ text "()"
    showAsOptimizedTerm (Sort _)	 = return $ text "()"
    showAsOptimizedTerm (MetaV id args)  = __IMPOSSIBLE__
    showAsOptimizedTerm (BlockedV bt)    = __IMPOSSIBLE__

----------------------------------------------------------------
--

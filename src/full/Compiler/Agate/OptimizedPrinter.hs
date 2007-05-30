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
    let defn = definitions ! name
    case theDef defn of
        Datatype np ni _ cnames s a ->
	    if ni > 0 then return empty -- __IMPOSSIBLE__
	      else do
	    	ty <- normalise $ defType defn
		dtypename <- showAsOptimizedType name
	    	dparams <- underDatatypeParameters np ty showTypeParameter
				(\_ -> return [])
	    	dargs <- mapM (showConstructorDeclaration definitions np) cnames
	    	showDatatypeDeclaration dtypename dparams dargs
	Record np clauses flds tel s a -> do
		let arity = np `div` 2
		ty <- normalise $ defType defn
		dtypename <- showAsOptimizedType name
	    	dparams <- underDatatypeParameters arity ty showTypeParameter
				(\_ -> return [])
	    	dcon <- showAsOptimizedConstructor name
		dflds <- mapM (showRecordFieldDeclaration definitions (arity + 1)) flds
		showDatatypeDeclaration dtypename dparams [sep $ dcon : dflds]
     	_ -> return empty -- TODO
    where
        showDatatypeDeclaration dtypename dparams [] =
	    return $ (text "type") <+> (sep (dtypename : dparams) <+> equals <+>
					text "()")
        showDatatypeDeclaration dtypename dparams dargs =
	    return $ (text "data") <+> (sep $
					sep (dtypename : dparams) <+> equals :
					punctuate (text " |") dargs)
				    $+$ text "    -- deriving (Show)"

showTypeParameter :: Doc -> Type -> TCM ([Doc] -> [Doc])
showTypeParameter dname ty = do
    ty <- instantiate ty
    (args,_) <- splitType ty
    case args of
	[]  -> return $ (:) dname
	_:_ -> do
		dk <- showAsOptimizedKind ty
		return $ (:) $ parens $ sep [ dname <+> text "::", dk ]

showRecordFieldDeclaration :: Definitions -> Int -> QName -> TCM Doc
showRecordFieldDeclaration definitions np fldname = do
    let defn = definitions ! fldname
    ty <- normalise $ defType defn
    underDatatypeParameters np ty (\d t -> return id) $ showAsOptimizedType

showConstructorDeclaration :: Definitions -> Int -> QName -> TCM Doc
showConstructorDeclaration definitions np cname = do
    dcon <- showAsOptimizedConstructor cname
    let defn = definitions ! cname
    ty <- normalise $ defType defn
    underDatatypeParameters np ty (\d t -> return id) $ \ty -> do
    	dargs <- forEachArgM showAsOptimizedType ty
    	return $ sep $ dcon : dargs

underDatatypeParameters :: Int -> Type ->
			   (Doc -> Type -> TCM (a -> a)) ->
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
	    dclauses <- mapM (showOptimizedClause name) clauses
	    return $ vcat $ dtypedecl : dclauses
	Datatype np ni _ cnames s a -> do
	    let dvars = map (\i -> text ("v" ++ show i)) [1 .. np + ni]
	    let dvaluedef = sep [ sep (dname : dvars), equals ] <+> text "()"
	    return $ dtypedecl $+$ dvaluedef
	Record np clauses flds tel s a -> 
	    return empty  -- no o_xxx since we always use D_xxx
	Constructor np _ qtname a ->
	    return empty  -- no o_xxx since we always use D_xxx
	Primitive a pf _ -> do
	    let dvaluedef = sep [ dname, equals ] <+>
			    sep [ text (show name), text "{- primitive -}" ]
	    return $ dtypedecl $+$ dvaluedef

--

underOptimizedClauseBody :: ClauseBody -> ([Doc] -> Term -> TCM Doc) -> TCM Doc
underOptimizedClauseBody body k = go 0 [] body where
    go n dvars NoBody        = return empty
    go n dvars (Body t)      = k dvars t
    go n dvars (NoBind body) = go n (dvars ++ [text "_"]) body
    go n dvars (Bind abs)    =
	underAbstraction_ abs{absName = show (n + 1)} $ \body -> do
	    dvar <- showAsOptimizedTerm $ Var 0 []
	    go (n + 1) (dvars ++ [dvar]) body

showOptimizedClause :: QName -> Clause -> TCM Doc
showOptimizedClause qname (Clause pats NoBody) = return empty
showOptimizedClause qname (Clause pats body)   = underOptimizedClauseBody body $
    \dvars term -> do
	dname <- showAsOptimizedTerm qname
	(_,dpats) <- showOptimizedPatterns dvars $ map unArg pats
	dbody <- showAsOptimizedTerm term
	return $ (sep (dname : dpats) <+> equals) <+> nest 2 dbody

showOptimizedPatterns :: [Doc] -> [Pattern] -> TCM ([Doc], [Doc])
showOptimizedPatterns dvars []           = return (dvars,[])
showOptimizedPatterns dvars (pat : pats) = do
    (dvars', dpat)  <- showOptimizedPattern  dvars  pat
    (dvars'',dpats) <- showOptimizedPatterns dvars' pats
    return (dvars'', (dpat : dpats))

showOptimizedPattern :: [Doc] -> Pattern -> TCM ([Doc], Doc)
showOptimizedPattern (dvar : dvars) (VarP s) = return (dvars, dvar)
showOptimizedPattern []             (VarP s) = return __IMPOSSIBLE__
showOptimizedPattern dvars (ConP qname args) = do
    dname <- showAsOptimizedConstructor qname
    (dvars',dargs) <- showOptimizedPatterns dvars (map unArg args)
    return (dvars', parens $ sep (dname : dargs))
showOptimizedPattern dvars (LitP lit) =
    return (dvars, showOptimizedLiteral lit)

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
	    Var _ _    -> return $ text "*"
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
    showAsOptimizedTerm (Def qname args) = do
	dname <- showAsOptimizedTerm qname
	dargs <- mapM (showAsOptimizedTerm . unArg) args
	return $ psep $ dname : dargs
    showAsOptimizedTerm (Con qname args) = do
    	dname <- showAsOptimizedConstructor qname
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

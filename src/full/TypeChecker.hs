
module TypeChecker where

import Control.Monad

import qualified Syntax.Abstract as A
import Syntax.Common
import Syntax.Info
import Syntax.Internal
import Syntax.Internal.Walk ()
import Syntax.Internal.Debug ()
import Syntax.Translation.AbstractToConcrete
import Syntax.Concrete.Pretty ()

import TypeChecking.Monad
import TypeChecking.Monad.Debug
import TypeChecking.Monad.Context
import TypeChecking.Constraints ()
import TypeChecking.Conversion ()
import TypeChecking.MetaVars
import TypeChecking.Reduce
import TypeChecking.Substitute

---------------------------------------------------------------------------
-- * Declarations
---------------------------------------------------------------------------

-- | Type check a sequence of declarations.
checkDecls :: [A.Declaration] -> TCM ()
checkDecls ds = mapM_ checkDecl ds


-- | Type check a single declaration.
checkDecl :: A.Declaration -> TCM ()
checkDecl d =
    case d of
	A.Axiom i x e		   -> checkAxiom i x e
	A.Synonym i x e loc	   -> checkSynonym i x e loc
	A.Definition i ts ds	   -> checkDefinition i ts ds
	A.Abstract i ds		   -> checkAbstract i ds
	A.Module i x tel ds	   -> checkModule i x tel ds
	A.ModuleDef i x tel m args -> checkModuleDef i x tel m args
	A.Import i x		   -> checkImport i x
	A.Open _		   -> return ()
	    -- open is just an artifact from the concrete syntax


-- | Type check an axiom.
checkAxiom :: DefInfo -> Name -> A.Expr -> TCM ()
checkAxiom _ x e =
    do	debug $ "checking axiom: " ++ show x ++ " : " ++ show (abstractToConcrete_ e)
	t <- isType e
	m <- currentModule
	debug $ "  current module: " ++ show m
	debug $ "  qualified name: " ++ show (qualify m x)
	addConstant (qualify m x) (Axiom t)


-- | Type check a synonym definition.
checkSynonym :: DefInfo -> Name -> A.Expr -> [A.Declaration] -> TCM ()
checkSynonym i x e loc =
    do	unless (null loc) $ fail "checkSynonym: local definitions not implemented"
	(v,t) <- inferExpr e
	m <- currentModule
	addConstant (qualify m x) (Synonym v t)


-- | Type check a definition by pattern matching.
checkDefinition :: DeclInfo -> [A.TypeSignature] -> [A.Definition] -> TCM ()
checkDefinition i ts ds = fail "checkDefinition: not implemented"


{-| Type check a block of declarations declared abstract.

    TODO: Declarations in this block should be tagged in some way, so that when
    we leave the current module we can hide the definitions. Also we need to
    hide the definition when checking the types of public things.
-}
checkAbstract :: DeclInfo -> [A.Declaration] -> TCM ()
checkAbstract _ ds = checkDecls ds


-- | Type check a module.
checkModule :: ModuleInfo -> ModuleName -> A.Telescope -> [A.Declaration] -> TCM ()
checkModule _ _ (_:_) _ = fail "checkModule: parameterised modules not implemented"
checkModule i x tel ds =
    do	m <- currentModule
	debug $ "checking module: " ++ show x
	let m' = A.qualifyModuleHack m x
	debug $ "  new current module: " ++ show m'
	withCurrentModule m' $ checkDecls ds


-- | Type check a module definition.
checkModuleDef :: ModuleInfo -> ModuleName -> A.Telescope -> ModuleName -> [Arg A.Expr] -> TCM ()
checkModuleDef i m tel m' args = fail "checkModuleDef: not implemented"


-- | Type check an import declaration. Goes away and reads the interface file.
--   Maybe it would be a good idea to have the scope checker store away the
--   interfaces so that we don't have to redo the work.
checkImport :: ModuleInfo -> ModuleName -> TCM ()
checkImport i m = fail "checkImport: not implemented"

---------------------------------------------------------------------------
-- * Sorts
---------------------------------------------------------------------------

isSort :: A.Expr -> TCM Sort
isSort e = fail "isSort: not implemented"


-- | Make sure that a type is a sort (instantiate meta variables if necessary).
forceSort :: Type -> TCM Sort
forceSort t =
    do	t' <- instType t
	case t of
	    Sort s	 -> return s
	    MetaT m args ->
		do  s <- newSortMeta
		    assign m args (Sort s)
		    return s
	    _	-> fail $ "not a sort " ++ show t


---------------------------------------------------------------------------
-- * Types
---------------------------------------------------------------------------

isType :: A.Expr -> TCM Type
isType e =
    case e of
	A.Prop _   -> return $ prop
	A.Set _ n  -> return $ set n
	A.Pi _ b e -> checkPiBinder b $ isType e
	_	   ->
	    do	(v,t) <- inferExpr e
		s <- forceSort t
		return $ El v s

checkPiBinder :: A.TypedBinding -> TCM Type -> TCM Type
checkPiBinder (A.TypedBinding _ h xs e) k =
    do	t <- isType e
	addCtxs xs t $
	    do	t' <- k
		return $ mkPi xs t t'
    where
	mkPi []	    _ t	= t
	mkPi (x:xs) s t = Pi s $ Abs (show x) $ mkPi xs (raise 1 s) t
	

---------------------------------------------------------------------------
-- * Terms
---------------------------------------------------------------------------

-- | Type check an expression.
checkExpr :: A.Expr -> Type -> TCM Value
checkExpr e t = fail "checkExpr: not implemented"


-- | Infer the type of an expression. Implemented by checking agains a meta
--   variable.
inferExpr :: A.Expr -> TCM (Value, Type)
inferExpr e =
    do	t <- newTypeMeta
	v <- checkExpr e t
	return (v,t)


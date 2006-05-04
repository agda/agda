
module TypeChecker where

import Control.Monad

import qualified Syntax.Abstract as A
import Syntax.Abstract.Pretty
import Syntax.Abstract.Views
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
import TypeChecking.Conversion
import TypeChecking.MetaVars
import TypeChecking.Reduce
import TypeChecking.Substitute

__debug x = debug x
__showA x = showA x

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
    do	t <- isType e
	m <- currentModule
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
	let m' = A.qualifyModuleHack m x
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

-- | Check that an expression is a sort. Used when checking datatypes.
isSort :: A.Expr -> TCM Sort
isSort e = fail "isSort: not implemented"


-- | Make sure that a type is a sort (instantiate meta variables if necessary).
forceSort :: Type -> TCM Sort
forceSort t =
    do	t' <- instType t
	case t' of
	    Sort s	 -> return s
	    MetaT m args ->
		do  s <- newSortMeta
		    assign m args (Sort s)
		    return s
	    _	-> fail $ "not a sort " ++ show t


---------------------------------------------------------------------------
-- * Types
---------------------------------------------------------------------------

-- | Check that an expression is a type.
isType :: A.Expr -> TCM Type
isType e =
    case e of
	A.Prop _   -> return $ prop
	A.Set _ n  -> return $ set n
	A.Pi _ b e -> checkPiBinder b $ isType e
	_	   -> inferTypeExpr e

-- | Check the binding in a 'A.Pi'. The second argument is run with the bound
--   variables in scope, and the resulting type is a 'Pi' ending in whatever
--   the second argument returns.
checkPiBinder :: A.TypedBinding -> TCM Type -> TCM Type
checkPiBinder b@(A.TypedBinding _ h xs e) k =
    do	t <- isType e
	addCtxs xs t $
	    do	t' <- k
		return $ mkPi xs t t'
    where
	mkPi []	    _ t	= t
	mkPi (x:xs) s t = Pi h s $ Abs (show x) $ mkPi xs (raise 1 s) t
	

---------------------------------------------------------------------------
-- * Terms
---------------------------------------------------------------------------

-- | Type check an expression.
checkExpr :: A.Expr -> Type -> TCM Term
checkExpr e t =
    case appView e of
	Application hd args ->
	    do	(v,t0) <- inferHead hd
		vs     <- checkArguments args t0 t
		return $ v `apply` vs
	_ ->
	    case e of
		A.Lam i b e	 -> fail "checkExpr: lambdas not implemented"
		A.QuestionMark i -> fail "checkExpr: question marks not implemented"
		A.Underscore i	 -> fail "checkExpr: underscores not implemented"
		A.Lit lit	 -> fail "checkExpr: literals not implemented"
		A.Let i ds e	 -> fail "checkExpr: let not implemented"
		_		 -> fail $ "not a proper term: " ++ show (abstractToConcrete_ e)


-- | Infer the type of a head thing (variable, function symbol, or constructor)
inferHead :: Head -> TCM (Term, Type)
inferHead (HeadVar _ x) =
    do	n <- varIndex x
	t <- typeOfBV n
	return (Var n [], t)
inferHead (HeadCon _ x) =
    do	t <- typeOfConst x
	return (Con x [], t)
inferHead (HeadDef _ x) =
    do	t <- typeOfConst x
	return (Def x [], t)


-- | Check a list of arguments: @checkArgs args t0 t1@ checks that
--   @t0 = Delta -> t1@ and @args : Delta@. Inserts hidden arguments to
--   make this happen.
checkArguments :: [Arg A.Expr] -> Type -> Type -> TCM Args
checkArguments [] t0 t1 = equalTyp () t0 t1 >> return []
checkArguments args t0 t1 = fail "checkArgs: not implemented"


-- | Infer the type of an expression. Implemented by checking agains a meta
--   variable.
inferExpr :: A.Expr -> TCM (Term, Type)
inferExpr e =
    do	t <- newTypeMeta
	v <- checkExpr e t
	return (v,t)

-- | Infer the sort of an expression which should be a type. Always returns 'El' something.
inferTypeExpr :: A.Expr -> TCM Type
inferTypeExpr e =
    do	s <- newSortMeta
	v <- checkExpr e (Sort s)
	return $ El v s


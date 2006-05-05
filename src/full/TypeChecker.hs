{-# OPTIONS -cpp #-}

module TypeChecker where

--import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as Map

import qualified Syntax.Abstract as A
import Syntax.Abstract.Pretty
import Syntax.Abstract.Views
import Syntax.Common
import Syntax.Info
--import Syntax.Position
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

import Utils.Monad

#include "undefined.h"

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
	m <- currentModule_
	addConstant (qualify m x) (Axiom t)


-- | Type check a synonym definition.
checkSynonym :: DefInfo -> Name -> A.Expr -> [A.Declaration] -> TCM ()
checkSynonym i x e loc =
    do	unless (null loc) $ fail "checkSynonym: local definitions not implemented"
	(v,t) <- inferExpr e
	m <- currentModule_
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
	A.Pi _ b e -> checkTypedBinding b $ \tel ->
			do  t <- isType e
			    return $ buildPi tel t
	_	   -> inferTypeExpr e

-- | Check a typed binding and extends the context with the bound variables.
--   The telescope passed to the continuation is valid in the original context.
checkTypedBinding :: A.TypedBinding -> ([Arg (String,Type)] -> TCM a) -> TCM a
checkTypedBinding b@(A.TypedBinding _ h xs e) ret =
    do	t <- isType e
	addCtxs xs t $ ret $ mkTel xs t
    where
	mkTel [] t     = []
	mkTel (x:xs) t = Arg h (show x,t) : mkTel xs (raise 1 t)


-- | Force a type to be a Pi. Instantiates if necessary. The 'Hiding' is only
--   used when instantiating a meta variable.
forcePi :: Hiding -> Type -> TCM Type
forcePi h t =
    do	t' <- instType t
	debug $ "forcePi " ++ show t
	debug $ "    --> " ++ show t'
	case t' of
	    Pi _ _ _	-> return t'
	    MetaT m vs	->
		do  s <- getSort t'
		    a <- newMeta (\m -> MetaT m []) $ UnderScoreT s []
		    b <- newMeta (\m -> MetaT m []) $ UnderScoreT s []
		    let n   = length vs
			ps  = map (\i -> Arg NotHidden (Var i [])) $ reverse [0 .. n - 1]
			ps' = Arg NotHidden (Var n []) : ps
		    let c = Pi h (a `apply` ps) $
			    Abs "x" $ b `apply` ps'
		    assign m vs c
		    instType t'
	    _		-> fail $ "Not a pi: " ++ show t

---------------------------------------------------------------------------
-- * Terms
---------------------------------------------------------------------------

-- | Type check an expression.
checkExpr :: A.Expr -> Type -> TCM Term
checkExpr e t =
    case appView e of
	Application hd args ->
	    do	--debug $ "checkExpr " ++ showA e ++ " : " ++ show t
		(v,t0) <- inferHead hd
		---debug $ "  head " ++ show v ++ " : " ++ show t0
		vs     <- checkArguments args t0 t
		--debug $ "  args " ++ show vs
		return $ v `apply` vs
	_ ->
	    case e of
		A.Lam i (A.DomainFull b) e ->
		    do	s  <- getSort t
			checkTypedBinding b $ \tel ->
			    do	t1 <- newTypeMeta s
				escapeContext (length tel) $ equalTyp () t (buildPi tel t1)
				v <- checkExpr e t1
				return $ buildLam (map name tel) v
		    where
			name (Arg h (x,_)) = Arg h x

		A.Lam i (A.DomainFree h x) e ->
		    do	t' <- forcePi h t
			case t' of
			    Pi h' a (Abs _ b) | h == h' ->
				addCtx x a $
				do  v <- checkExpr e b
				    return $ Lam (Abs (show x) v) []
			    _	-> fail $ "expected " ++ show h ++ " function space, found " ++ show t'

		A.QuestionMark i -> newQuestionMark t
		A.Underscore i	 -> newValueMeta t
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
checkArguments []   t0 t1 =
    do	t0' <- instType t0
	t1' <- instType t1
	case t0' of
	    Pi Hidden a b | notMetaOrHPi t1'  ->
		    do	v  <- newValueMeta a
			vs <- checkArguments [] (substAbs v b) t1'
			return $ Arg Hidden v : vs
	    _ ->    do	equalTyp () t0' t1'
			return []
    where
	notMetaOrHPi (MetaT _ _)     = False
	notMetaOrHPi (Pi Hidden _ _) = False
	notMetaOrHPi _		     = True

checkArguments (Arg h e : args) t0 t1 =
    do	t0' <- forcePi h t0
	case (h, t0') of
	    (NotHidden, Pi Hidden a b) ->
		do  u  <- newValueMeta a
		    us <- checkArguments (Arg h e : args) (substAbs u b) t1
		    return $ Arg Hidden u : us
	    (_, Pi h' a b) | h == h' ->
		do  u  <- checkExpr e a
		    us <- checkArguments args (substAbs u b) t1
		    return $ Arg h u : us
	    (Hidden, Pi NotHidden _ _) ->
		fail $ "can't give hidden argument " ++ showA e ++ " to something of type " ++ show t0
	    _ -> __IMPOSSIBLE__


-- | Infer the type of an expression. Implemented by checking agains a meta
--   variable.
inferExpr :: A.Expr -> TCM (Term, Type)
inferExpr e =
    do	t <- newTypeMeta_
	v <- checkExpr e t
	return (v,t)

-- | Infer the sort of an expression which should be a type. Always returns 'El' something.
inferTypeExpr :: A.Expr -> TCM Type
inferTypeExpr e =
    do	s <- newSortMeta
	v <- checkExpr e (Sort s)
	return $ El v s

---------------------------------------------------------------------------
-- * To be moved somewhere else
---------------------------------------------------------------------------

-- | Get the sort of a type. Should be moved somewhere else.
getSort :: Type -> TCM Sort
getSort t =
    do	t' <- instType t
	case t' of
	    El _ s	     -> return s
	    Pi _ a (Abs _ b) -> Lub <$> getSort a <*> getSort b
	    Sort s	     -> sSuc s
	    MetaT m _	     ->
		do  store <- gets stMetaStore
		    case Map.lookup m store of
			Just (UnderScoreT s _) -> return s
			Just (HoleT s _)       -> return s
			_		       -> __IMPOSSIBLE__
	    LamT _	    -> __IMPOSSIBLE__

buildPi :: [Arg (String,Type)] -> Type -> Type
buildPi tel t = foldr (\ (Arg h (x,a)) b -> Pi h a (Abs x b) ) t tel

buildLam :: [Arg String] -> Term -> Term
buildLam xs t = foldr (\ (Arg _ x) t -> Lam (Abs x t) []) t xs

-- | Get the next higher sort. Move somewhere else and do some reductions
--   (@suc (set n) --> suc (set (n + 1))@)
sSuc :: Sort -> TCM Sort
sSuc = return . Suc


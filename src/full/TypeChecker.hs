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
import Syntax.Position
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
import Utils.List

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
	A.Definition i ts ds	   -> checkMutual i ts ds
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


-- | Type check a bunch of mutual inductive recursive definitions.
checkMutual :: DeclInfo -> [A.TypeSignature] -> [A.Definition] -> TCM ()
checkMutual i ts ds =
    do	mapM_ checkTypeSignature ts
	mapM_ checkDefinition ds


-- | Type check the type signature of an inductive or recursive definition.
checkTypeSignature :: A.TypeSignature -> TCM ()
checkTypeSignature (A.Axiom i x e) = checkAxiom i x e
checkTypeSignature _ = __IMPOSSIBLE__	-- type signatures are always axioms


-- | Check an inductive or recursive definition. Assumes the type has has been
--   checked and added to the signature.
checkDefinition (A.FunDef i x cs)     = checkFunDef i x cs
checkDefinition (A.DataDef i x ps cs) = checkDataDef i x ps cs

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
-- * Datatypes
---------------------------------------------------------------------------

-- | Type check a datatype definition. Assumes that the type has already been
--   checked.
checkDataDef :: DefInfo -> Name -> [A.LamBinding] -> [A.Constructor] -> TCM ()
checkDataDef i x ps cs =
    do	m	<- currentModule_
	let name  = qualify m x
	    npars = length ps
	Axiom t <- getConstInfo name
	bindParameters ps t $ \s ->
	    do	mapM_ (checkConstructor name npars s) cs
		addConstant name (Datatype t npars $ map (cname m) cs)
    where
	cname m (A.Axiom _ x _) = qualify m x
	cname _ _		= __IMPOSSIBLE__ -- constructors are axioms


-- | Type check a constructor declaration. Checks that the constructor targets
--   the datatype and that it fits inside the declared sort.
checkConstructor :: QName -> Int -> Sort -> A.Constructor -> TCM ()
checkConstructor d npars s (A.Axiom i c e) =
    do	t  <- isType e
	s' <- getSort t
	s' `leqSort` s
	t `constructs` d
	m <- currentModule_
	addConstant (qualify m c) (Constructor t npars d)
checkConstructor _ _ _ _ = __IMPOSSIBLE__ -- constructors are axioms


-- | Bind the parameters of a datatype. The bindings should be domain free.
bindParameters :: [A.LamBinding] -> Type -> (Sort -> TCM a) -> TCM a
bindParameters [] (Sort s) ret = ret s
bindParameters [] _ _ = __IMPOSSIBLE__ -- the syntax prohibits anything but a sort here
bindParameters (A.DomainFree h x : ps) (Pi h' a b) ret
    | h /= h'	=
	__IMPOSSIBLE__
    | otherwise = addCtx x a $ bindParameters ps (absBody b) ret
bindParameters _ _ _ = __IMPOSSIBLE__


-- | Check that a type constructs something of the given datatype.
--   TODO: what if there's a meta here?
constructs :: Type -> QName -> TCM ()
constructs (Pi _ _ b) d = constructs (absBody b) d
constructs (El (Def d' _) _) d
    | d == d'	= return ()
constructs t d = fail $ show t ++ " should be application of " ++ show d


-- | Force a type to be a specific datatype.
forceData :: QName -> Type -> TCM Type
forceData d t =
    do	t' <- instType t
	case t' of
	    El (Def d' _) _
		| d == d'   -> return t'
	    MetaT m vs	    ->
		do  Datatype t n _ <- getConstInfo d
		    ps <- newArgsMeta t
		    s  <- getSort t'
		    assign m vs $ El (Def d ps) s
		    instType t'
	    _		    -> fail $ show t ++ " should be application of " ++ show d

---------------------------------------------------------------------------
-- * Definitions by pattern matching
---------------------------------------------------------------------------

-- | Type check a definition by pattern matching.
checkFunDef :: DefInfo -> Name -> [A.Clause] -> TCM ()
checkFunDef i x cs =

    do	-- Get the type of the function
	name	<- flip qualify x <$> currentModule_
	Axiom t <- getConstInfo name

	-- Check that all clauses have the same number of arguments
	unless (allEqual $ map npats cs) $ fail $ "equations give different arities for function " ++ show x

	-- Check the clauses
	cs' <- mapM (checkClause t) cs

	-- Add the definition
	m   <- currentModule_
	addConstant (qualify m x) $ Function cs' t
    where
	npats (A.Clause (A.LHS _ _ ps) _ _) = length ps


-- | Type check a function clause.
checkClause :: Type -> A.Clause -> TCM Clause
checkClause _ (A.Clause _ _ (_:_))  = fail "checkClause: local definitions not implemented"
checkClause t (A.Clause (A.LHS i x ps) rhs []) =
    checkPatterns ps t $ \xs ps t' ->
	do  v <- checkExpr rhs t'
	    return $ Clause ps $ foldr (\x t -> Bind $ Abs x t) (Body v) xs


-- | Check the patterns of a left-hand-side. Binds the variables of the pattern.
--   TODO: add hidden arguments.
checkPatterns :: [Arg A.Pattern] -> Type -> ([String] -> [Arg Pattern] -> Type -> TCM a) -> TCM a
checkPatterns [] t ret	   = ret [] [] t
checkPatterns (Arg h p:ps) t ret =
    do	t' <- forcePi h t
	case t' of
	    Pi h' a b | h == h' ->
		checkPattern p a    $ \xs p' ->
		do  v <- patToTerm p'
		    checkPatterns ps (substAbs v b) $ \ys ps' t'' ->
			ret (xs ++ ys) (Arg h p':ps') t''
	    _ -> fail $ show t ++ " should be a " ++ show h ++ " function type"


-- | Type check a pattern and bind the variables.
checkPattern :: A.Pattern -> Type -> ([String] -> Pattern -> TCM a) -> TCM a
checkPattern (A.VarP x) t ret =
    addCtx x t $ ret [show x] (VarP x)
checkPattern (A.WildP i) t ret =
    do	x <- freshNoName (getRange i)
	addCtx x t $ ret [show x] (VarP x)
checkPattern (A.ConP i c ps) t ret =
    do	Constructor t' n d <- getConstInfo c
	El (Def _ vs) _ <- forceData d t
	checkPatterns ps (substs (map unArg vs) t') $ \xs ps' _ ->
	    ret xs (ConP c ps')


---------------------------------------------------------------------------
-- * Sorts
---------------------------------------------------------------------------

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


-- | Check that the first sort is less or equal to the second.
--   The second sort is always 'Prop' or @'Type' n@.
leqSort :: Sort -> Sort -> TCM ()
leqSort s1 s2 =
    do	s1' <- instSort s1
	s2' <- instSort s2
	case (s1',s2') of
	    (Prop, Prop)	      -> return ()
	    (Prop, Type n)   | n >= 1 -> return ()
	    (Type n, Type m) | n <= m -> return ()
	    (Lub s1a s1b, _)	      -> leqSort s1a s2' >> leqSort s1b s2'
	    (Suc s, Type n)  | n >= 1 -> leqSort s (Type $ n - 1)
	    (MetaS m, _)	      -> setRef () m (InstS s2')
	    _			      -> fail $ show s1 ++ " is not less or equal to " ++ show s2

---------------------------------------------------------------------------
-- * Types
---------------------------------------------------------------------------

-- | Check that an expression is a type.
isType :: A.Expr -> TCM Type
isType e =
    case e of
	A.Prop _	 -> return $ prop
	A.Set _ n	 -> return $ set n
	A.Pi _ b e	 ->
	    checkTypedBinding b $ \tel ->
		do  t <- isType e
		    return $ buildPi tel t
	A.QuestionMark _ -> newQuestionMarkT_
	A.Underscore _	 -> newTypeMeta_
	_		 -> inferTypeExpr e

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
-- 	debug $ "forcePi " ++ show t
-- 	debug $ "    --> " ++ show t'
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


-- | Infer the sort of an expression which should be a type. Always returns 'El' something.
inferTypeExpr :: A.Expr -> TCM Type
inferTypeExpr e =
    do	s <- newSortMeta
	v <- checkExpr e (Sort s)
	return $ El v s


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
    do	Constructor t n d <- getConstInfo x
	t0		  <- newTypeMeta_   -- TODO: not so nice
	El (Def _ vs) _	  <- forceData d t0
	return (Con x [], substs (map unArg vs) t)
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


unArg :: Arg a -> a
unArg (Arg _ x) = x


-- | Convert a pattern to a term.
patToTerm :: Pattern -> TCM Term
patToTerm (VarP x) =
    do	n <- varIndex x
	return $ Var n []
patToTerm (ConP c ps) = Con c <$> mapM patToTerm' ps
    where
	patToTerm' (Arg h p) = Arg h <$> patToTerm p


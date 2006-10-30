{-# OPTIONS -cpp -fglasgow-exts #-}

module TypeChecker where

import Prelude hiding (putStrLn, putStr, print)

--import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import qualified Data.Map as Map
import qualified Data.List as List
import System.Directory
import System.Time

import qualified Syntax.Abstract as A
import Syntax.Abstract.Pretty
import Syntax.Abstract.Views
import Syntax.Common
import Syntax.Info as Info
import Syntax.Position
import Syntax.Internal
import Syntax.Translation.AbstractToConcrete
import Syntax.Translation.ConcreteToAbstract
import Syntax.Concrete.Pretty ()
import Syntax.Strict
import Syntax.Literal
import Syntax.Scope

import TypeChecking.Monad hiding (defAbstract)
import qualified TypeChecking.Monad as TCM
import TypeChecking.Monad.Name
import TypeChecking.Monad.Builtin
import TypeChecking.Conversion
import TypeChecking.MetaVars
import TypeChecking.Reduce
import TypeChecking.Substitute
import TypeChecking.Primitive
import TypeChecking.Rebind
import TypeChecking.Serialise
import TypeChecking.Interface
import TypeChecking.Constraints
import TypeChecking.Errors

import Utils.Monad
import Utils.List
import Utils.Serialise
import Utils.IO

#include "undefined.h"

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
	A.Primitive i x e	   -> checkPrimitive i x e
	A.Definition i ts ds	   -> checkMutual i ts ds
	A.Module i x tel ds	   -> checkModule i x tel ds
	A.ModuleDef i x tel m args -> checkModuleDef i x tel m args
	A.Import i x		   -> checkImport i x
	A.Pragma i p		   -> checkPragma i p
	A.Open _		   -> return ()
	    -- open is just an artifact from the concrete syntax


-- | Type check an axiom.
checkAxiom :: DefInfo -> Name -> A.Expr -> TCM ()
checkAxiom _ x e =
    do	t <- isType_ e
	m <- currentModule
	addConstant (qualify m x) (Defn t 0 Axiom)


-- | Type check a primitive function declaration.
checkPrimitive :: DefInfo -> Name -> A.Expr -> TCM ()
checkPrimitive i x e =
    traceCall (CheckPrimitive (getRange i) x e) $ do
    PrimImpl t' pf <- lookupPrimitiveFunction (nameString x)
    t <- isType_ e
    noConstraints $ equalType t t'
    m <- currentModule
    let s  = show x
	qx = qualify m x
    bindPrimitive s $ pf { primFunName = qx }
    addConstant qx (Defn t 0 $ Primitive (defAbstract i) s [])
    where
	nameString (Name _ x) = show x


-- | Check a pragma.
checkPragma :: Range -> A.Pragma -> TCM ()
checkPragma r p =
    traceCall (CheckPragma r p) $ case p of
	A.BuiltinPragma x e -> bindBuiltin x e
	A.OptionsPragma _   -> __IMPOSSIBLE__	-- not allowed here

-- | Type check a bunch of mutual inductive recursive definitions.
checkMutual :: DeclInfo -> [A.TypeSignature] -> [A.Definition] -> TCM ()
checkMutual i ts ds =
    do	mapM_ checkTypeSignature ts
	mapM_ checkDefinition ds


-- | Type check the type signature of an inductive or recursive definition.
checkTypeSignature :: A.TypeSignature -> TCM ()
checkTypeSignature (A.Axiom i x e) =
    case defAccess i of
	PublicAccess	-> inAbstractMode $ checkAxiom i x e
	_		-> checkAxiom i x e
checkTypeSignature _ = __IMPOSSIBLE__	-- type signatures are always axioms


-- | Check an inductive or recursive definition. Assumes the type has has been
--   checked and added to the signature.
checkDefinition d =
    case d of
	A.FunDef i x cs	    -> abstract (defAbstract i) $ checkFunDef i x cs
	A.DataDef i x ps cs -> abstract (defAbstract i) $ checkDataDef i x ps cs
    where
	-- Concrete definitions cannot use information about abstract things.
	abstract ConcreteDef = inAbstractMode
	abstract _	     = id


-- | Type check a module.
checkModule :: ModuleInfo -> ModuleName -> A.Telescope -> [A.Declaration] -> TCM ()
checkModule i x tel ds =
    do	tel0 <- getContextTelescope
	checkTelescope tel $ \tel' ->
	    do	m'   <- flip qualifyModule x <$> currentModule
		reportLn 5 $ "adding module " ++ show (mnameId m')
		addModule m' $ ModuleDef
				{ mdefName	= m'
				, mdefTelescope = tel0 ++ tel'
				, mdefNofParams = length tel'
				, mdefDefs	= Map.empty
				}
		withCurrentModule m' $ checkDecls ds


{-| Type check a module definition.
    If M' is qualified we know that its parent is fully instantiated. In other
    words M' is a valid module in a prefix of the current context.

    Current context: ΓΔ

    Without bothering about submodules of M':
	Γ   ⊢ module M' Ω
	ΓΔ  ⊢ module M Θ = M' us
	ΓΔΘ ⊢ us : Ω

	Expl ΓΩ _ = lookupModule M'
	addModule M ΓΔΘ = M' Γ us

    Submodules of M':

	Forall submodules A
	    ΓΩΦ ⊢ module M'.A Ψ ...

	addModule M.A ΓΔΘΦΨ = M'.A Γ us ΦΨ
-}
checkModuleDef :: ModuleInfo -> ModuleName -> A.Telescope -> ModuleName -> [Arg A.Expr] -> TCM ()
checkModuleDef i x tel m' args =
    do	m <- flip qualifyModule x <$> currentModule
	gammaDelta <- getContextTelescope
	md' <- lookupModule m'
	let gammaOmega	  = mdefTelescope md'
	    (gamma,omega) = splitAt (length gammaOmega - mdefNofParams md') gammaOmega
	    delta	  = drop (length gamma) gammaDelta
	checkTelescope tel $ \theta ->
	    do	(vs, cs) <- checkArguments_ (getRange m') args omega
		noConstraints (return cs)   -- we don't allow left-over constraints in module instantiations
		let vs0 = reverse [ Arg Hidden
				  $ Var (i + length delta + length theta) []
				  | i <- [0..length gamma - 1]
				  ]
		addModule m $ ModuleDef
				    { mdefName	     = m
				    , mdefTelescope  = gammaDelta ++ theta
				    , mdefNofParams  = length theta
				    , mdefDefs	     = implicitModuleDefs
							(gammaDelta ++ theta)
							m' (vs0 ++ vs)
							(mdefDefs md')
				    }
		forEachModule_ (`isSubModuleOf` m') $ \m'a ->
		    do	md <- lookupModule m'a	-- lookup twice (could be optimised)
			let gammaOmegaPhiPsi = mdefTelescope md
			    ma = requalifyModule m' m m'a
			    phiPsi  = drop (length gammaOmega) gammaOmegaPhiPsi
			    vs1	    = reverse [ Arg Hidden $ Var i []
					      | i <- [0..length phiPsi - 1]
					      ]
			    tel	    = gammaDelta ++ theta ++ phiPsi
			addModule ma $ ModuleDef
					    { mdefName	     = ma
					    , mdefTelescope  = tel
					    , mdefNofParams  = mdefNofParams md
					    , mdefDefs	     = implicitModuleDefs
								tel m'a (vs0 ++ vs ++ vs1)
								(mdefDefs md)
					    }


-- | Type check an import declaration. Actually doesn't do anything, since all
--   the work is done when scope checking.
checkImport :: ModuleInfo -> ModuleName -> TCM ()
checkImport i x = return ()

---------------------------------------------------------------------------
-- * Datatypes
---------------------------------------------------------------------------

-- | Type check a datatype definition. Assumes that the type has already been
--   checked.
checkDataDef :: DefInfo -> Name -> [A.LamBinding] -> [A.Constructor] -> TCM ()
checkDataDef i x ps cs =
    traceCall (CheckDataDef (getRange i) x ps cs) $ do
	m <- currentModule
	let name  = qualify m x
	    npars = length ps
	t <- typeOfConst name
	s <- bindParameters ps t $ \tel s ->
	    do	let tel' = map hide tel
		mapM_ (checkConstructor name tel' s) cs
		return s
	do  proofIrr <- proofIrrelevance
	    s	     <- reduce s
	    case (proofIrr, s, cs) of
		(True, Prop, _:_:_) -> typeError PropMustBeSingleton
		_		    -> return ()
	addConstant name (Defn t 0 $ Datatype npars (map (cname m) cs)
					      s (defAbstract i)
			 )
    where
	cname m (A.Axiom _ x _) = qualify m x
	cname _ _		= __IMPOSSIBLE__ -- constructors are axioms

	hide (Arg _ x) = Arg Hidden x

-- | Type check a constructor declaration. Checks that the constructor targets
--   the datatype and that it fits inside the declared sort.
checkConstructor :: QName -> Telescope -> Sort -> A.Constructor -> TCM ()
checkConstructor d tel s con@(A.Axiom i c e) =
    traceCall (CheckConstructor d tel s con) $ do
	t <- isType_ e
	t `constructs` d
	t `fitsIn` s
	m <- currentModule
	escapeContext (length tel)
	    $ addConstant (qualify m c)
	    $ Defn (telePi tel t) 0 $ Constructor (length tel) d $ defAbstract i
checkConstructor _ _ _ _ = __IMPOSSIBLE__ -- constructors are axioms


-- | Bind the parameters of a datatype. The bindings should be domain free.
bindParameters :: [A.LamBinding] -> Type -> (Telescope -> Sort -> TCM a) -> TCM a
bindParameters [] (El _ (Sort s)) ret = ret [] s
bindParameters [] _ _ = __IMPOSSIBLE__ -- the syntax prohibits anything but a sort here
bindParameters (A.DomainFree h x : ps) (El _ (Pi (Arg h' a) b)) ret	-- always dependent function
    | h /= h'	=
	__IMPOSSIBLE__
    | otherwise = addCtx x a $ bindParameters ps (absBody b) $ \tel s ->
		    ret (Arg h (show x,a) : tel) s
bindParameters _ _ _ = __IMPOSSIBLE__


-- | Check that the arguments to a constructor fits inside the sort of the datatype.
--   The first argument is the type of the constructor.
fitsIn :: Type -> Sort -> TCM ()
fitsIn t s =
    do	t <- instantiate t
	case funView $ unEl t of
	    FunV (Arg h a) _ -> do
		let s' = getSort a
		s' `leqSort` s
		x <- freshName_ (argName t)
		let v  = Arg h $ Var 0 []
		    t' = piApply' (raise 1 t) [v]
		addCtx x a $ fitsIn t' s
	    _		     -> return ()

-- | Check that a type constructs something of the given datatype.
--   TODO: what if there's a meta here?
constructs :: Type -> QName -> TCM ()
constructs t q = constrT 0 t
    where
	constrT n (El s v) = constr n s v

	constr n s v = do
	    v <- reduce v
	    case v of
		Pi a b	-> underAbstraction (unArg a) b $ \t ->
			   constrT (n + 1) t
		Fun _ b -> constrT n b
		Def d vs
		    | d == q -> checkParams n =<< reduce vs
		_ -> bad $ El s v

	bad t = typeError $ ShouldEndInApplicationOfTheDatatype t

	checkParams n vs
	    | vs `sameVars` ps = return ()
	    | otherwise	       =
		typeError $ ShouldBeAppliedToTheDatatypeParameters
			    (apply def ps) (apply def vs)
	    where
		def = Def q []
		ps = reverse [ Arg h $ Var i [] | (i,Arg h _) <- zip [n..] vs ]
		sameVar (Var i []) (Var j []) = i == j
		sameVar _ _		      = False
		sameVars xs ys = and $ zipWith sameVar (map unArg xs) (map unArg ys)


-- | Force a type to be a specific datatype.
forceData :: QName -> Type -> TCM Type
forceData d (El s0 t) = do
    t' <- reduce t
    case t' of
	Def d' _
	    | d == d'   -> return $ El s0 t'
	MetaV m vs	    -> do
	    Defn t _ (Datatype n _ s _) <- getConstInfo d
	    ps <- newArgsMeta t
	    noConstraints $ equalType (El s0 t') (El s (Def d ps)) -- TODO: too strict?
	    reduce $ El s0 t'
	_ -> typeError $ ShouldBeApplicationOf (El s0 t) d

---------------------------------------------------------------------------
-- * Definitions by pattern matching
---------------------------------------------------------------------------

-- | Type check a definition by pattern matching.
checkFunDef :: DefInfo -> Name -> [A.Clause] -> TCM ()
checkFunDef i x cs =

    traceCall (CheckFunDef (getRange i) x cs) $ do
	-- Get the type of the function
	name <- flip qualify x <$> currentModule
	t    <- typeOfConst name

	-- Check the clauses
	cs <- mapM (checkClause t) cs

	-- Check that all clauses have the same number of arguments
	unless (allEqual $ map npats cs) $ typeError DifferentArities

	-- Annotate the clauses with which arguments are actually used.
	cs <- mapM rebindClause cs

	-- Add the definition
	addConstant name $ Defn t 0 $ Function cs $ defAbstract i
    where
	npats (Clause ps _) = length ps


-- | Type check a function clause.
checkClause :: Type -> A.Clause -> TCM Clause
checkClause t c@(A.Clause (A.LHS i x aps) rhs ds) =
    traceCall (CheckClause t c) $
    checkPatterns aps t $ \ (xs, ps, ts, t') -> do
	checkDecls ds
	body <- case rhs of
	    A.RHS e -> do
		v <- checkExpr e t'
		return $ foldr (\x t -> Bind $ Abs x t) (Body v) xs
	    A.AbsurdRHS
		| any (containsAbsurdPattern . unArg) aps
			    -> return NoBody
		| otherwise -> typeError $ NoRHSRequiresAbsurdPattern aps
	return $ Clause ps body

-- | Check if a pattern contains an absurd pattern. For instance, @suc ()@
containsAbsurdPattern :: A.Pattern -> Bool
containsAbsurdPattern p = case p of
    A.VarP _	  -> False
    A.ConP _ _ ps -> any (containsAbsurdPattern . unArg) ps
    A.WildP _	  -> False
    A.AsP _ _ p   -> containsAbsurdPattern p
    A.AbsurdP _   -> True
    A.LitP _	  -> False
    A.DefP _ _ _  -> __IMPOSSIBLE__


-- | Check the patterns of a left-hand-side. Binds the variables of the pattern.
checkPatterns :: [Arg A.Pattern] -> Type -> (([String], [Arg Pattern], [Arg Term], Type) -> TCM a) -> TCM a
checkPatterns [] t ret =
    traceCallCPS (CheckPatterns [] t) ret $ \ret -> do
    t' <- instantiate t
    case funView $ unEl t' of
	FunV (Arg Hidden _) _   -> do
	    r <- getCurrentRange
	    checkPatterns [Arg Hidden $ A.WildP $ PatRange r] t' ret
	_ -> ret ([], [], [], t)
checkPatterns ps0@(Arg h p:ps) t ret =
    traceCallCPS (CheckPatterns ps0 t) ret $ \ret -> do
    (t', cs) <- forcePi h (name p) t
    addNewConstraints cs
    case (h,funView $ unEl t') of
	(NotHidden, FunV (Arg Hidden _) _) ->
	    checkPatterns (Arg Hidden (A.WildP $ PatRange $ getRange p) : Arg h p : ps) t' ret
	(_, FunV (Arg h' a) _) | h == h' ->
	    checkPattern (argName t') p a $ \ (xs, p, v) -> do
	    let t0 = raise (length xs) t'
	    checkPatterns ps (piApply' t0 [Arg h' v]) $ \ (ys, ps, vs, t'') -> do
		let v' = raise (length ys) v
		ret (xs ++ ys, Arg h p : ps, Arg h v':vs, t'')
	_ -> typeError $ WrongHidingInLHS t'
    where
	name (A.VarP x) = show x
	name _	        = "x"

-- | TODO: move
argName = argN . unEl
    where
	argN (Pi _ b)  = "_" ++ absName b
	argN (Fun _ _) = "_"
	argN _	  = __IMPOSSIBLE__


actualConstructor :: QName -> TCM QName
actualConstructor c = do
    v <- constructorForm =<< reduce (Con c [])
    case ignoreBlocking v of
	Con c _	-> return c
	_	-> actualConstructor =<< stripLambdas v
    where
	stripLambdas v = case ignoreBlocking v of
	    Con c _ -> return c
	    Lam _ b -> do
		x <- freshName_ $ absName b
		addCtx x (sort Prop) $ stripLambdas (absBody b)
	    _	    -> typeError $ GenericError $ "Not a constructor: " ++ show c

-- | Type check a pattern and bind the variables. First argument is a name
--   suggestion for wildcard patterns.
checkPattern :: String -> A.Pattern -> Type -> (([String], Pattern, Term) -> TCM a) -> TCM a
checkPattern name p t ret =
    traceCallCPS (CheckPattern name p t) ret $ \ret -> case p of
	A.VarP x    ->
	    addCtx x t $ ret ([show x], VarP (show x), Var 0 [])
	A.WildP i   -> do
	    x <- freshName (getRange i) name
	    addCtx x t $ ret ([name], VarP name, Var 0 [])
	A.ConP i c ps -> do
	    c <- actualConstructor c
	    Defn t' _ (Constructor _ d _) <- getConstInfo c -- don't instantiate this
	    El _ (Def _ vs)		  <- forceData d t  -- because this guy won't be
	    Con c' us			  <- constructorForm =<< reduce (Con c $ map hide vs)
	    checkPatterns ps (piApply' t' vs) $ \ (xs, ps', ts', rest) -> do
		let n  = length xs
		    tn = raise n t
		v  <- blockTerm tn (Con c' $ raise n us ++ ts') $ equalType rest tn
		ret (xs, ConP c' ps', v)
	    where
		hide (Arg _ x) = Arg Hidden x
	A.AbsurdP i -> do
	    isEmptyType t
	    x <- freshName (getRange i) name    -- TODO: actually do something about absurd patterns
	    addCtx x t $ ret ([show x], AbsurdP, Var 0 [])
	A.AsP i x p ->
	    checkPattern name p t $ \ (xs, p, v) ->
	    addLetBinding x v (raise (length xs) t) $ ret (xs, p, v)
	A.LitP l    -> do
	    v <- checkLiteral l t
	    ret ([], LitP l, v)
	A.DefP i f ps ->
	    typeError $ NotImplemented "defined patterns"


-- | Make sure that a type is empty. TODO: Move.
isEmptyType :: Type -> TCM ()
isEmptyType t = do
    t <- reduce t
    case t of
	El _ (Def d _) -> do
	    Defn _ _ di <- getConstInfo d
	    case di of
		Datatype _ [] _ _ -> return ()
		_		  -> notEmpty t
	_ -> notEmpty t
    where
	notEmpty t = typeError $ ShouldBeEmpty t

---------------------------------------------------------------------------
-- * Let bindings
---------------------------------------------------------------------------

checkLetBindings :: [A.LetBinding] -> TCM a -> TCM a
checkLetBindings = foldr (.) id . map checkLetBinding

checkLetBinding :: A.LetBinding -> TCM a -> TCM a
checkLetBinding b@(A.LetBind i x t e) ret =
    traceCallCPS_ (CheckLetBinding b) ret $ \ret -> do
	t <- isType_ t
	v <- checkExpr e t
	addLetBinding x v t ret

---------------------------------------------------------------------------
-- * Types
---------------------------------------------------------------------------

-- | Check that an expression is a type.
isType :: A.Expr -> Sort -> TCM Type
isType e s =
    traceCall (IsTypeCall e s) $ do
    v <- checkExpr e (sort s)
    return $ El s v

-- | Check that an expression is a type without knowing the sort.
isType_ :: A.Expr -> TCM Type
isType_ e =
    traceCall (IsType_ e) $ do
    s <- newSortMeta
    isType e s


-- | Force a type to be a Pi. Instantiates if necessary. The 'Hiding' is only
--   used when instantiating a meta variable.
forcePi :: Hiding -> String -> Type -> TCM (Type, Constraints)
forcePi h name (El s t) =
    do	t' <- reduce t
	case t' of
	    Pi _ _	-> return (El s t', [])
	    Fun _ _	-> return (El s t', [])
	    MetaV m vs	-> do
		i <- getMetaInfo <$> lookupMeta m

		sa <- newSortMeta
		sb <- newSortMeta
		let s' = sLub sa sb

		a <- newTypeMeta sa
		x <- refreshName (getRange i) name
		b <- addCtx x a $ newTypeMeta sb

		let ty = El s' $ Pi (Arg h a) (Abs (show x) b)
		cs <- equalType (El s t') ty
		ty' <- reduce ty
		return (ty', cs)
	    _ -> typeError $ ShouldBePi (El s t')


---------------------------------------------------------------------------
-- * Telescopes
---------------------------------------------------------------------------

-- | Type check a telescope. Binds the variables defined by the telescope.
checkTelescope :: A.Telescope -> (Telescope -> TCM a) -> TCM a
checkTelescope [] ret = ret []
checkTelescope (b : tel) ret =
    checkTypedBindings b $ \tel1 ->
    checkTelescope tel   $ \tel2 ->
	ret $ tel1 ++ tel2


-- | Check a typed binding and extends the context with the bound variables.
--   The telescope passed to the continuation is valid in the original context.
checkTypedBindings :: A.TypedBindings -> (Telescope -> TCM a) -> TCM a
checkTypedBindings (A.TypedBindings i h bs) ret =
    thread checkTypedBinding bs $ \bss ->
    ret $ map (Arg h) (concat bss)

checkTypedBinding :: A.TypedBinding -> ([(String,Type)] -> TCM a) -> TCM a
checkTypedBinding (A.TBind i xs e) ret = do
    t <- isType_ e
    addCtxs xs t $ ret $ mkTel xs t
    where
	mkTel [] t     = []
	mkTel (x:xs) t = (show x,t) : mkTel xs (raise 1 t)
checkTypedBinding (A.TNoBind e) ret = do
    t <- isType_ e
    ret [("_",t)]


---------------------------------------------------------------------------
-- * Terms
---------------------------------------------------------------------------

-- | Type check an expression.
checkExpr :: A.Expr -> Type -> TCM Term
checkExpr e t =
    traceCall (CheckExpr e t) $ do
    t <- instantiate t
    case e of

	-- Variable or constant application
	_   | Application hd args <- appView e -> do
		(v,  t0)     <- inferHead hd
		(vs, t1, cs) <- checkArguments (getRange hd) args t0 t
		blockTerm t (apply v vs) $ (cs ++) <$> equalType t1 t

	-- Insert hidden lambda if appropriate
	_   | not (hiddenLambda e)
	    , FunV (Arg Hidden _) _ <- funView (unEl t) -> do
		x <- freshName r (argName t)
		checkExpr (A.Lam (ExprRange $ getRange e) (A.DomainFree Hidden x) e) t
	    where
		r = emptyR (rStart $ getRange e)
		    where
			emptyR r = Range r r

		hiddenLambda (A.Lam _ (A.DomainFree Hidden _) _)		     = True
		hiddenLambda (A.Lam _ (A.DomainFull (A.TypedBindings _ Hidden _)) _) = True
		hiddenLambda _							     = False

	A.App i e arg -> do
	    (v0, t0)	 <- inferExpr e
	    (vs, t1, cs) <- checkArguments (getRange e) [arg] t0 t
	    blockTerm t (apply v0 vs) $ (cs ++) <$> equalType t1 t

	A.Lam i (A.DomainFull b) e ->
	    checkTypedBindings b $ \tel -> do
	    t1 <- newTypeMeta_
	    cs <- escapeContext (length tel) $ equalType t (telePi tel t1)
	    v <- checkExpr e t1
	    blockTerm t (buildLam (map name tel) v) (return cs)
	    where
		name (Arg h (x,_)) = Arg h x

	A.Lam i (A.DomainFree h x) e0 -> do
	    (t',cs) <- forcePi h (show x) t
	    case funView $ unEl t' of
		FunV (Arg h' a) _
		    | h == h' ->
			addCtx x a $ do
			let arg = Arg h (Var 0 [])
			    tb  = raise 1 t' `piApply'` [arg]
			v <- checkExpr e0 tb
			blockTerm t (Lam h (Abs (show x) v)) (return cs)
		    | otherwise ->
			typeError $ WrongHidingInLambda t'
		_   -> __IMPOSSIBLE__

	A.QuestionMark i -> do
	    setScope (Info.metaScope i)
	    newQuestionMark  t
	A.Underscore i   -> do
	    setScope (Info.metaScope i)
	    newValueMeta t

	A.Lit lit    -> checkLiteral lit t
	A.Let i ds e -> checkLetBindings ds $ checkExpr e t
	A.Pi _ tel e ->
	    checkTelescope tel $ \tel -> do
	    t' <- telePi tel <$> isType_ e
	    blockTerm t (unEl t') $ equalType (sort $ getSort t') t
	A.Fun _ (Arg h a) b -> do
	    a' <- isType_ a
	    b' <- isType_ b
	    let s = getSort a' `sLub` getSort b'
	    blockTerm t (Fun (Arg h a') b') $ equalType (sort s) t
	A.Set _ n    ->
	    blockTerm t (Sort (Type n)) $ equalType (sort $ Type $ n + 1) t
	A.Prop _     ->
	    blockTerm t (Sort Prop) $ equalType (sort $ Type 1) t
	A.Var _ _    -> __IMPOSSIBLE__
	A.Def _ _    -> __IMPOSSIBLE__
	A.Con _ _    -> __IMPOSSIBLE__


-- | Infer the type of a head thing (variable, function symbol, or constructor)
inferHead :: Head -> TCM (Term, Type)
inferHead (HeadVar _ x) = traceCall (InferVar x) $ getVarInfo x
inferHead (HeadCon i x) = inferDef Con i x
inferHead (HeadDef i x) = inferDef Def i x

inferDef :: (QName -> Args -> Term) -> NameInfo -> QName -> TCM (Term, Type)
inferDef mkTerm i x =
    traceCall (InferDef (getRange i) x) $ do
    d  <- getConstInfo x
    d' <- instantiateDef d
    gammaDelta <- getContextTelescope
    let t     = defType d'
	gamma = take (defFreeVars d) gammaDelta
	k     = length gammaDelta - defFreeVars d
	vs    = reverse [ Arg h $ Var (i + k) []
			| (Arg h _,i) <- zip gamma [0..]
			]
    return (mkTerm x vs, t)


-- | Check a list of arguments: @checkArgs args t0 t1@ checks that
--   @t0 = Delta -> t0'@ and @args : Delta@. Inserts hidden arguments to
--   make this happen. Returns @t0'@ and any constraints that have to be
--   solve for everything to be well-formed.
checkArguments :: Range -> [Arg A.Expr] -> Type -> Type -> TCM (Args, Type, Constraints)
checkArguments r [] t0 t1 =
    traceCall (CheckArguments r [] t0 t1) $ do
	t0' <- reduce t0
	t1' <- reduce t1
	case funView $ unEl t0' of -- TODO: clean
	    FunV (Arg Hidden a) _ | notHPi $ unEl t1'  -> do
		v  <- newValueMeta a
		let arg = Arg Hidden v
		(vs, t0'',cs) <- checkArguments r [] (piApply' t0' [arg]) t1'
		return (arg : vs, t0'',cs)
	    _ -> return ([], t0', [])
    where
	notHPi (Pi  (Arg Hidden _) _) = False
	notHPi (Fun (Arg Hidden _) _) = False
	notHPi _		      = True

checkArguments r args0@(Arg h e : args) t0 t1 =
    traceCall (CheckArguments r args0 t0 t1) $ do
	(t0', cs) <- forcePi h (name e) t0
	case (h, funView $ unEl t0') of
	    (NotHidden, FunV (Arg Hidden a) _) -> do
		u  <- newValueMeta a
		let arg = Arg Hidden u
		(us, t0'',cs') <- checkArguments r (Arg h e : args)
				       (piApply' t0' [arg]) t1
		return (arg : us, t0'', cs ++ cs')
	    (_, FunV (Arg h' a) _) | h == h' -> do
		u  <- checkExpr e a
		let arg = Arg h u
		(us, t0'', cs') <- checkArguments (fuseRange r e) args (piApply' t0' [arg]) t1
		return (arg : us, t0'', cs ++ cs')
	    (Hidden, FunV (Arg NotHidden _) _) ->
		typeError $ WrongHidingInApplication t0'
	    _ -> __IMPOSSIBLE__
    where
	name (A.Var _ x) = show x
	name _	         = "x"


-- | Check that a list of arguments fits a telescope.
checkArguments_ :: Range -> [Arg A.Expr] -> Telescope -> TCM (Args, Constraints)
checkArguments_ r args tel = do
    (args, _, cs) <- checkArguments r args (telePi tel $ sort Prop) (sort Prop)
    return (args, cs)


-- | Infer the type of an expression. Implemented by checking agains a meta
--   variable.
inferExpr :: A.Expr -> TCM (Term, Type)
inferExpr e = do
    t <- newTypeMeta_
    v <- checkExpr e t
    return (v,t)

---------------------------------------------------------------------------
-- * Literal
---------------------------------------------------------------------------

checkLiteral :: Literal -> Type -> TCM Term
checkLiteral lit t = do
    t' <- litType lit
    v  <- blockTerm t (Lit lit) $ equalType t t'
    return v
    where
	el t = El (Type 0) t
	litType l = case l of
	    LitInt _ _	  -> el <$> primNat
	    LitFloat _ _  -> el <$> primFloat
	    LitChar _ _   -> el <$> primChar
	    LitString _ _ -> el <$> primString

---------------------------------------------------------------------------
-- * Checking builtin pragmas
---------------------------------------------------------------------------

bindBuiltinType :: String -> A.Expr -> TCM ()
bindBuiltinType b e = do
    t <- checkExpr e (sort $ Type 0)
    bindBuiltinName b t

bindBuiltinBool :: String -> A.Expr -> TCM ()
bindBuiltinBool b e = do
    bool <- primBool
    t	 <- checkExpr e $ El (Type 0) bool
    bindBuiltinName b t

-- | Bind something of type @Set -> Set@.
bindBuiltinType1 :: String -> A.Expr -> TCM ()
bindBuiltinType1 thing e = do
    let set	 = sort (Type 0)
	setToSet = El (Type 1) $ Fun (Arg NotHidden set) set
    f <- checkExpr e setToSet
    bindBuiltinName thing f

bindBuiltinZero :: A.Expr -> TCM ()
bindBuiltinZero e = do
    nat  <- primNat
    zero <- checkExpr e (El (Type 0) nat)
    bindBuiltinName builtinZero zero

bindBuiltinSuc :: A.Expr -> TCM ()
bindBuiltinSuc e = do
    nat  <- primNat
    let	nat' = El (Type 0) nat
	natToNat = El (Type 0) $ Fun (Arg NotHidden nat') nat'
    suc <- checkExpr e natToNat
    bindBuiltinName builtinSuc suc

-- | Built-in nil should have type @{A:Set} -> List A@
bindBuiltinNil :: A.Expr -> TCM ()
bindBuiltinNil e = do
    list' <- primList
    let set	= sort (Type 0)
	list a	= El (Type 0) (list' `apply` [Arg NotHidden a])
	nilType = telePi [Arg Hidden ("A",set)] $ list (Var 0 [])
    nil <- checkExpr e nilType
    bindBuiltinName builtinNil nil

-- | Built-in cons should have type @{A:Set} -> A -> List A -> List A@
bindBuiltinCons :: A.Expr -> TCM ()
bindBuiltinCons e = do
    list' <- primList
    let set	  = sort (Type 0)
	el	  = El (Type 0)
	a	  = Var 0 []
	list x	  = el $ list' `apply` [Arg NotHidden x]
	hPi x a b = telePi [Arg Hidden (x,a)] b
	fun a b	  = el $ Fun (Arg NotHidden a) b
	consType  = hPi "A" set $ el a `fun` (list a `fun` list a)
    cons <- checkExpr e consType
    bindBuiltinName builtinCons cons

bindBuiltinPrimitive :: String -> String -> A.Expr -> (Term -> TCM ()) -> TCM ()
bindBuiltinPrimitive name builtin e@(A.Def _ qx) verify = do
    PrimImpl t pf <- lookupPrimitiveFunction name
    v <- checkExpr e t

    verify v

    info <- getConstInfo qx
    let cls = defClauses info
	a   = TCM.defAbstract info
    bindPrimitive name $ pf { primFunName = qx }
    addConstant qx $ info { theDef = Primitive a name cls }

    -- needed? yes, for checking equations for mul
    bindBuiltinName builtin v
bindBuiltinPrimitive _ b _ _ = typeError $ GenericError $ "Builtin " ++ b ++ " must be bound to a function"

builtinPrimitives :: [ (String, (String, Term -> TCM ())) ]
builtinPrimitives =
    [ "NATPLUS"   |-> ("primNatPlus", verifyPlus)
    , "NATMINUS"  |-> ("primNatMinus", verifyMinus)
    , "NATTIMES"  |-> ("primNatTimes", verifyTimes)
    , "NATDIVSUC" |-> ("primNatDivSuc", verifyDivSuc)
    , "NATMODSUC" |-> ("primNatModSuc", verifyModSuc)
    , "NATEQUALS" |-> ("primNatEquals", verifyEquals)
    , "NATLESS"	  |-> ("primNatLess", verifyLess)
    ]
    where
	(|->) = (,)

	verifyPlus plus =
	    verify ["n","m"] $ \(@@) zero suc (==) choice -> do
		let m = Var 0 []
		    n = Var 1 []
		    x + y = plus @@ x @@ y

		-- We allow recursion on any argument
		choice
		    [ do n + zero  == n
			 n + suc m == suc (n + m)
		    , do suc n + m == suc (n + m)
			 zero  + m == m
		    ]

	verifyMinus minus =
	    verify ["n","m"] $ \(@@) zero suc (==) choice -> do
		let m = Var 0 []
		    n = Var 1 []
		    x - y = minus @@ x @@ y

		-- We allow recursion on any argument
		zero  - m     == zero
		suc n - zero  == suc n
		suc n - suc m == (n - m)

	verifyTimes times = do
	    plus <- primNatPlus
	    verify ["n","m"] $ \(@@) zero suc (==) choice -> do
		let m = Var 0 []
		    n = Var 1 []
		    x + y = plus  @@ x @@ y
		    x * y = times @@ x @@ y

		choice
		    [ do n * zero == zero
			 choice [ (n * suc m) == (n + (n * m))
				, (n * suc m) == ((n * m) + n)
				]
		    , do zero * n == zero
			 choice [ (suc n * m) == (m + (n * m))
				, (suc n * m) == ((n * m) + m)
				]
		    ]

	verifyDivSuc ds =
	    verify ["n","m"] $ \(@@) zero suc (==) choice -> do
		minus <- primNatMinus
		let x - y      = minus @@ x @@ y
		    divSuc x y = ds @@ x @@ y
		    m	       = Var 0 []
		    n	       = Var 1 []

		divSuc  zero   m == zero
		divSuc (suc n) m == suc (divSuc (n - m) m)

	verifyModSuc ms =
	    verify ["n","m"] $ \(@@) zero suc (==) choice -> do
		minus <- primNatMinus
		let x - y      = minus @@ x @@ y
		    modSuc x y = ms @@ x @@ y
		    m	       = Var 0 []
		    n	       = Var 1 []
		modSuc  zero   m == zero
		modSuc (suc n) m == modSuc (n - m) m

	verifyEquals eq =
	    verify ["n","m"] $ \(@@) zero suc (===) choice -> do
	    true  <- primTrue
	    false <- primFalse
	    let x == y = eq @@ x @@ y
		m      = Var 0 []
		n      = Var 1 []
	    (zero  == zero ) === true
	    (suc n == suc m) === (n == m)
	    (suc n == zero ) === false
	    (zero  == suc n) === false

	verifyLess leq =
	    verify ["n","m"] $ \(@@) zero suc (===) choice -> do
	    true  <- primTrue
	    false <- primFalse
	    let x < y = leq @@ x @@ y
		m     = Var 0 []
		n     = Var 1 []
	    (n     < zero)  === false
	    (suc n < suc m) === (n < m)
	    (zero  < suc m) === true

	verify :: [String] -> ( (Term -> Term -> Term) -> Term -> (Term -> Term) ->
				(Term -> Term -> TCM ()) ->
				([TCM ()] -> TCM ()) -> TCM a) -> TCM a
	verify xs f = do
	    nat	 <- El (Type 0) <$> primNat
	    zero <- primZero
	    s    <- primSuc
	    let x @@ y = x `apply` [Arg NotHidden y]
		x == y = noConstraints $ equalTerm nat x y
		suc n  = s @@ n
		choice = foldr1 (\x y -> x `catchError` \_ -> y)
	    xs <- mapM freshName_ xs
	    addCtxs xs nat $ f (@@) zero suc (==) choice

-- | Bind a builtin thing to an expression.
bindBuiltin :: String -> A.Expr -> TCM ()
bindBuiltin b e = do
    top <- null <$> getContextTelescope
    unless top $ typeError $ BuiltinInParameterisedModule b
    bind b e
    where
	bind b e
	    | elem b builtinTypes		 = bindBuiltinType b e
	    | elem b [builtinTrue, builtinFalse] = bindBuiltinBool b e
	    | elem b [builtinList, builtinIO]	 = bindBuiltinType1 b e
	    | b == builtinNil			 = bindBuiltinNil e
	    | b == builtinCons			 = bindBuiltinCons e
	    | b == builtinZero			 = bindBuiltinZero e
	    | b == builtinSuc			 = bindBuiltinSuc e
	    | Just (s,v) <- lookup b builtinPrimitives =
		bindBuiltinPrimitive s b e v
	    | otherwise				 = typeError $ NoSuchBuiltinName b

---------------------------------------------------------------------------
-- * To be moved somewhere else
---------------------------------------------------------------------------

buildLam :: [Arg String] -> Term -> Term
buildLam xs t = foldr (\ (Arg h x) t -> Lam h (Abs x t)) t xs



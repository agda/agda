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
import Syntax.Info as Info
import Syntax.Position
import Syntax.Internal
import Syntax.Internal.Walk ()
import Syntax.Internal.Debug ()
import Syntax.Translation.AbstractToConcrete
import Syntax.Concrete.Pretty ()

import TypeChecking.Monad
import TypeChecking.Monad.Context
import TypeChecking.Constraints ()
import TypeChecking.Conversion
import TypeChecking.MetaVars
import TypeChecking.Reduce
import TypeChecking.Substitute

import TypeChecking.Monad.Debug

import Utils.Monad
import Utils.List

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
	A.Definition i ts ds	   -> checkMutual i ts ds
	A.Module i x tel ds	   -> checkModule i x tel ds
	A.ModuleDef i x tel m args -> checkModuleDef i x tel m args
	A.Import i x		   -> checkImport i x
	A.Open _		   -> return ()
	    -- open is just an artifact from the concrete syntax


-- | Type check an axiom.
checkAxiom :: DefInfo -> Name -> A.Expr -> TCM ()
checkAxiom _ x e =
    do	t <- isType_ e
	m <- currentModule
	n <- asks (length . envContext)
	addConstant (qualify m x) (Defn t n Axiom)


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
	    do	--debug $ "module " ++ show m ++ " " ++ show theta ++ " = " ++ show m' ++ " " ++ show args
		--debug $ "module " ++ show m' ++ " " ++ show gamma ++ show omega
		vs <- checkArguments_ (getRange m') args omega
		let vs0 = reverse [ Arg Hidden
				  $ Var (i + length delta + length theta) []
				  | i <- [0..length gamma - 1]
				  ]
		qm <- flip qualifyModule m <$> currentModule
		addModule qm $ ModuleDef
				    { mdefName	     = qm
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
    do	m <- currentModule
	let name  = qualify m x
	    npars = length ps
	t <- typeOfConst name
	n <- asks $ length . envContext
	s <- bindParameters ps t $ \_ s ->
	    do	mapM_ (checkConstructor name npars s) cs
		return s
	addConstant name (Defn t n $ Datatype npars (map (cname m) cs)
					      s (defAbstract i)
			 )
    where
	cname m (A.Axiom _ x _) = qualify m x
	cname _ _		= __IMPOSSIBLE__ -- constructors are axioms


-- | Type check a constructor declaration. Checks that the constructor targets
--   the datatype and that it fits inside the declared sort.
checkConstructor :: QName -> Int -> Sort -> A.Constructor -> TCM ()
checkConstructor d npars s (A.Axiom i c e) =
    do	t  <- isType_ e
	s' <- getSort t
	s' `leqSort` s
	t  `constructs` d
	m <- currentModule
	n <- asks $ length . envContext
	addConstant (qualify m c) $
	    Defn t (n - npars) $ Constructor npars d $ defAbstract i
checkConstructor _ _ _ _ = __IMPOSSIBLE__ -- constructors are axioms


-- | Bind the parameters of a datatype. The bindings should be domain free.
bindParameters :: [A.LamBinding] -> Type -> (Telescope -> Sort -> TCM a) -> TCM a
bindParameters [] (Sort s) ret = ret [] s
bindParameters [] _ _ = __IMPOSSIBLE__ -- the syntax prohibits anything but a sort here
bindParameters (A.DomainFree h x : ps) (Pi h' a b) ret
    | h /= h'	=
	__IMPOSSIBLE__
    | otherwise = addCtx x a $ bindParameters ps (absBody b) $ \tel s ->
		    ret (Arg h a : tel) s
bindParameters _ _ _ = __IMPOSSIBLE__


-- | Check that a type constructs something of the given datatype.
--   TODO: what if there's a meta here?
constructs :: Type -> QName -> TCM ()
constructs t q = constr 0 t q
    where
	constr n (Pi _ _ b) d = constr (n + 1) (absBody b) d
	constr n (El (Def d' vs) _) d
	    | d == d'	= checkParams n . map unArg =<< reduce vs
	constr _ t d = fail $ show t ++ " should be application of " ++ show d

	checkParams n vs
	    | vs `sameVars` ps = return ()
	    | otherwise	       = fail $ show q ++ " should be applied to its parameters in the target of a constructor"
				    ++ show vs ++ show ps
	    where
		ps = reverse [ Var i [] | (i,_) <- zip [n..] vs ]
		sameVar (Var i []) (Var j []) = i == j
		sameVar _ _		      = False
		sameVars xs ys = and $ zipWith sameVar xs ys


-- | Force a type to be a specific datatype.
forceData :: QName -> Type -> TCM Type
forceData d t =
    do	t' <- reduce t
	case t' of
	    El (Def d' _) _
		| d == d'   -> return t'
	    MetaT m vs	    ->
		do  Defn t _ (Datatype n _ s _) <- getConstInfo d
		    ps <- newArgsMeta t
		    s' <- getSort t'
		    equalSort s s'
		    equalTyp () t' $ El (Def d ps) s
		    reduce t'
	    _		    -> fail $ show t ++ " should be application of " ++ show d

---------------------------------------------------------------------------
-- * Definitions by pattern matching
---------------------------------------------------------------------------

-- | Type check a definition by pattern matching.
checkFunDef :: DefInfo -> Name -> [A.Clause] -> TCM ()
checkFunDef i x cs =

    do	-- Get the type of the function
	name <- flip qualify x <$> currentModule
	t    <- typeOfConst name

	-- Check the clauses
	cs' <- mapM (checkClause t) cs

	-- Check that all clauses have the same number of arguments
	unless (allEqual $ map npats cs') $ fail $ "equations give different arities for function " ++ show x

	-- Add the definition
	m   <- currentModule
	n   <- asks $ length . envContext
	addConstant (qualify m x) $ Defn t n $ Function cs' $ defAbstract i
    where
	npats (Clause ps _) = length ps


-- | Type check a function clause.
checkClause :: Type -> A.Clause -> TCM Clause
checkClause _ (A.Clause _ _ (_:_))  = fail "checkClause: local definitions not implemented"
checkClause t (A.Clause (A.LHS i x ps) rhs ds) =
    do	setCurrentRange i
	checkPatterns ps t $ \xs ps _ t' ->
	    do  checkDecls ds
		v <- checkExpr rhs t'
		return $ Clause ps $ foldr (\x t -> Bind $ Abs x t) (Body v) xs


-- | Check the patterns of a left-hand-side. Binds the variables of the pattern.
--   TODO: add hidden arguments.
checkPatterns :: [Arg A.Pattern] -> Type -> ([String] -> [Arg Pattern] -> [Arg Term] -> Type -> TCM a) -> TCM a
checkPatterns [] t ret	   =
    do	t' <- instantiate t
	case t' of
	    Pi Hidden a b   ->
		do  r <- getCurrentRange
		    checkPatterns [Arg Hidden $ A.WildP $ PatRange r] t' ret
	    _		    -> ret [] [] [] t
checkPatterns (Arg h p:ps) t ret =
    do	setCurrentRange p
	t' <- forcePi h t
	case (h,t') of
	    (NotHidden, Pi Hidden _ _) ->
		checkPatterns (Arg Hidden (A.WildP $ PatRange $ getRange p) : Arg h p : ps) t' ret
	    (_,Pi h' a b) | h == h' ->
		checkPattern p a $ \xs p' v ->
		do  let b' = raise (length xs) b
		    checkPatterns ps (absApp v b') $ \ys ps' vs t'' ->
			do  let v' = raise (length ys) v
			    ret (xs ++ ys) (Arg h p':ps')(Arg h v':vs) t''
	    _ -> fail $ show t ++ " should be a " ++ show h ++ " function type"


-- | Type check a pattern and bind the variables.
checkPattern :: A.Pattern -> Type -> ([String] -> Pattern -> Term -> TCM a) -> TCM a
checkPattern (A.VarP x) t ret =
    addCtx x t $ ret [show x] (VarP $ show x) (Var 0 [])
checkPattern (A.WildP i) t ret =
    do	x <- freshNoName (getRange i)
	addCtx x t $ ret [show x] (VarP "_") (Var 0 [])
checkPattern (A.ConP i c ps) t ret =
    do	setCurrentRange i
	Defn t' _ (Constructor n d _) <- getConstInfo c -- don't instantiate this
	El (Def _ vs) _		      <- forceData d t	-- because this guy won't be
	Con c' us		      <- reduce $ Con c vs
	checkPatterns ps (piApply t' vs) $ \xs ps' ts' rest ->
	    do	equalTyp () rest (raise (length xs) t)
		ret xs (ConP c' ps') (Con c' $ us ++ ts')


---------------------------------------------------------------------------
-- * Sorts
---------------------------------------------------------------------------

-- | Make sure that a type is a sort (instantiate meta variables if necessary).
forceSort :: Range -> Type -> TCM Sort
forceSort r t =
    do	setCurrentRange r
	t' <- reduce t
	case t' of
	    Sort s	 -> return s
	    MetaT m args ->
		do  s <- newSortMeta
		    equalTyp () t' (Sort s)
		    return s
	    _	-> fail $ "not a sort " ++ show t


---------------------------------------------------------------------------
-- * Types
---------------------------------------------------------------------------

-- | Check that an expression is a type.
isType :: A.Expr -> Sort -> TCM Type
isType e s =
    do	setCurrentRange e
	t <- case e of
		A.Prop _	 -> return $ prop
		A.Set _ n	 -> return $ set n
		A.Pi _ b e	 ->
		    checkTypedBinding b $ \tel ->
			do  t <- isType_ e
			    return $ buildPi tel t
		A.QuestionMark i -> 
		    do  setScope (Info.metaScope i)
			newQuestionMarkT s
		A.Underscore i	 -> 
		    do  setScope (Info.metaScope i)
			newTypeMeta s
		_		 ->
		    do	v <- checkExpr e (Sort s)
			return $ El v s
	s' <- getSort t
	equalSort s s'
	return t


-- | Check that an expression is a type without knowing the sort.
isType_ :: A.Expr -> TCM Type
isType_ e =
    do	setCurrentRange e
	s <- newSortMeta
	isType e s


-- | Force a type to be a Pi. Instantiates if necessary. The 'Hiding' is only
--   used when instantiating a meta variable.
forcePi :: Hiding -> Type -> TCM Type
forcePi h t =
    do	t' <- reduce t
-- 	debug $ "forcePi " ++ show t'
	case t' of
	    Pi _ _ _	-> return t'
	    MetaT m vs	->
		do  s <- getSort t'
		    i <- getMetaInfo <$> lookupMeta m

		    sa <- newSortMeta
		    sb <- newSortMeta
		    equalSort s (sLub sa sb)

		    a <- newTypeMeta sa
		    x <- freshName (getRange i) "x"
		    b <- addCtx x a $ newTypeMeta sb
		    
		    equalTyp () t' $ Pi h a (Abs "x" b)
		    reduce t'
	    _		-> fail $ "Not a pi: " ++ show t


---------------------------------------------------------------------------
-- * Telescopes
---------------------------------------------------------------------------

-- | Type check a telescope. Binds the variables defined by the telescope.
checkTelescope :: A.Telescope -> (Telescope -> TCM a) -> TCM a
checkTelescope [] ret = ret []
checkTelescope (b : tel) ret =
    checkTypedBinding b $ \xs ->
    checkTelescope tel  $ \tel' ->
	ret $ map (fmap snd) xs ++ tel'


-- | Check a typed binding and extends the context with the bound variables.
--   The telescope passed to the continuation is valid in the original context.
checkTypedBinding :: A.TypedBinding -> ([Arg (String,Type)] -> TCM a) -> TCM a
checkTypedBinding b@(A.TypedBinding i h xs e) ret =
    do	t <- isType_ e
	addCtxs xs t $ ret $ mkTel xs t
    where
	mkTel [] t     = []
	mkTel (x:xs) t = Arg h (show x,t) : mkTel xs (raise 1 t)


---------------------------------------------------------------------------
-- * Terms
---------------------------------------------------------------------------

-- | Type check an expression.
checkExpr :: A.Expr -> Type -> TCM Term
checkExpr e t =
    do	setCurrentRange e
	case appView e of
	    Application hd args ->
		do  
		    ctx <- getContext
-- 		    debug $ "checkExpr " ++ showA e ++ " : " ++ show t
-- 		    debug $ "       in\n" ++ unlines (map (("   " ++) . show) ctx)
		    (v,t0) <- inferHead hd
-- 		    debug $ "  head " ++ show v ++ " : " ++ show t0
		    vs     <- checkArguments (getRange hd) args t0 t
-- 		    debug $ "  args " ++ show vs
		    return $ v `apply` vs
	    _ ->
		case e of
		    A.Lam i (A.DomainFull b) e ->
			checkTypedBinding b $ \tel ->
			    do  t1 <- newTypeMeta_
				escapeContext (length tel) $ equalTyp () t (buildPi tel t1)
				v <- checkExpr e t1
				return $ buildLam (map name tel) v
			where
			    name (Arg h (x,_)) = Arg h x

		    A.Lam i (A.DomainFree h x) e ->
			do  t' <- forcePi h t
			    case t' of
				Pi h' a (Abs _ b) | h == h' ->
				    addCtx x a $
				    do  v <- checkExpr e b
					return $ Lam (Abs (show x) v) []
				_	-> fail $ "expected " ++ show h ++ " function space, found " ++ show t'

		    A.QuestionMark i -> 
                        do  setScope (Info.metaScope i)
                            newQuestionMark  t
		    A.Underscore i   -> 
                        do  setScope (Info.metaScope i)
                            newValueMeta t
		    A.Lit lit	     -> fail "checkExpr: literals not implemented"
		    A.Let i ds e     -> fail "checkExpr: let not implemented"
		    _		     -> fail $ "not a proper term: " ++ show (abstractToConcrete_ e)


-- | Infer the type of a head thing (variable, function symbol, or constructor)
inferHead :: Head -> TCM (Term, Type)
inferHead (HeadVar _ x) =
    do	setCurrentRange x
	n <- varIndex x
	t <- typeOfBV n
	return (Var n [], t)
inferHead (HeadCon i x) = inferDef Con i x
inferHead (HeadDef i x) = inferDef Def i x

inferDef :: (QName -> Args -> Term) -> NameInfo -> QName -> TCM (Term, Type)
inferDef mkTerm i x =
    do	setCurrentRange x
	d <- instantiateDef =<< getConstInfo x
	gammaDelta <- getContextTelescope
	let t	  = defType d
	    gamma = take (defFreeVars d) gammaDelta
	    k	  = length gammaDelta - defFreeVars d
	    vs	  = reverse [ Arg h $ Var (i + k) []
			    | (Arg h _,i) <- zip gamma [0..]
			    ]
-- 	debug $ "inferDef " ++ show x ++ " : " ++ show t ++ " = " ++ show (Def x vs)
	return (mkTerm x vs, t)


-- | Check a list of arguments: @checkArgs args t0 t1@ checks that
--   @t0 = Delta -> t1@ and @args : Delta@. Inserts hidden arguments to
--   make this happen.
checkArguments :: Range -> [Arg A.Expr] -> Type -> Type -> TCM Args
checkArguments r [] t0 t1 =
    do	setCurrentRange r
	t0' <- reduce t0
	t1' <- reduce t1
	case t0' of
	    Pi Hidden a b | notMetaOrHPi t1'  ->
		    do	v  <- newValueMeta a
			vs <- checkArguments r [] (absApp v b) t1'
			return $ Arg Hidden v : vs
	    _ ->    do	equalTyp () t0' t1'
			return []
    where
	notMetaOrHPi (MetaT _ _)     = False
	notMetaOrHPi (Pi Hidden _ _) = False
	notMetaOrHPi _		     = True

checkArguments r (Arg h e : args) t0 t1 =
    do	setCurrentRange r
	t0' <- forcePi h t0
	case (h, t0') of
	    (NotHidden, Pi Hidden a b) ->
		do  u  <- newValueMeta a
		    us <- checkArguments r (Arg h e : args) (absApp u b) t1
		    return $ Arg Hidden u : us
	    (_, Pi h' a b) | h == h' ->
		do  u  <- checkExpr e a
		    us <- checkArguments (fuseRange r e) args (absApp u b) t1
		    return $ Arg h u : us
	    (Hidden, Pi NotHidden _ _) ->
		fail $ "can't give hidden argument " ++ showA e ++ " to something of type " ++ show t0
	    _ -> __IMPOSSIBLE__


-- | Check that a list of arguments fits a telescope.
checkArguments_ :: Range -> [Arg A.Expr] -> Telescope -> TCM Args
checkArguments_ r args tel =
    checkArguments r args (telePi tel $ Sort Prop) (Sort Prop)


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

buildPi :: [Arg (String,Type)] -> Type -> Type
buildPi tel t = foldr (\ (Arg h (x,a)) b -> Pi h a (Abs x b) ) t tel

buildLam :: [Arg String] -> Term -> Term
buildLam xs t = foldr (\ (Arg _ x) t -> Lam (Abs x t) []) t xs



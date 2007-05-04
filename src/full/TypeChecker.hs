{-# OPTIONS -cpp -fglasgow-exts #-}

module TypeChecker where

import Prelude hiding (putStrLn, putStr, print)

--import Control.Monad
import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List
import Data.Traversable (traverse)
import System.Directory
import System.Time

import qualified Syntax.Abstract as A
import Syntax.Abstract.Views
import qualified Syntax.Abstract.Pretty as A
import Syntax.Common
import Syntax.Info as Info
import Syntax.Position
import Syntax.Internal
import Syntax.Translation.AbstractToConcrete
import Syntax.Translation.ConcreteToAbstract
import Syntax.Concrete.Pretty ()
import Syntax.Strict
import Syntax.Literal
import Syntax.Scope.Base

import TypeChecking.Monad hiding (defAbstract)
import qualified TypeChecking.Monad as TCM
import TypeChecking.Monad.Builtin
import TypeChecking.Conversion
import TypeChecking.MetaVars
import TypeChecking.Reduce
import TypeChecking.Substitute
import TypeChecking.Primitive
import TypeChecking.Rebind
import TypeChecking.Serialise
import TypeChecking.Constraints
import TypeChecking.Errors
import TypeChecking.Positivity
import TypeChecking.Empty
import TypeChecking.Patterns.Monad
import TypeChecking.Free
import TypeChecking.Pretty
import TypeChecking.Records

import Utils.Monad
import Utils.List
import Utils.Serialise
import Utils.IO
import Utils.Tuple
import Utils.Function
import Utils.Size

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
	A.Axiom i x e		 -> checkAxiom i x e
	A.Primitive i x e	 -> checkPrimitive i x e
	A.Definition i ts ds	 -> checkMutual i ts ds
	A.Section i x tel ds	 -> checkSection i x tel ds
	A.Apply i x m args rd rm -> checkSectionApplication i x m args rd rm
	A.Import i x		 -> checkImport i x
	A.Pragma i p		 -> checkPragma i p
	A.ScopedDecl scope ds	 -> setScope scope >> checkDecls ds
	    -- open is just an artifact from the concrete syntax


-- | Type check an axiom.
checkAxiom :: DefInfo -> QName -> A.Expr -> TCM ()
checkAxiom _ x e =
    do	t <- isType_ e
	addConstant x (Defn x t Axiom)


-- | Type check a primitive function declaration.
checkPrimitive :: DefInfo -> QName -> A.Expr -> TCM ()
checkPrimitive i x e =
    traceCall (CheckPrimitive (getRange i) (qnameName x) e) $ do  -- TODO!! (qnameName)
    PrimImpl t' pf <- lookupPrimitiveFunction (nameString $ qnameName x)
    t <- isType_ e
    noConstraints $ equalType t t'
    let s  = show $ nameConcrete $ qnameName x
    bindPrimitive s $ pf { primFunName = x }
    addConstant x (Defn x t $ Primitive (defAbstract i) s [])
    where
	nameString (Name _ x _ _) = show x


-- | Check a pragma.
checkPragma :: Range -> A.Pragma -> TCM ()
checkPragma r p =
    traceCall (CheckPragma r p) $ case p of
	A.BuiltinPragma x e -> bindBuiltin x e
	A.OptionsPragma _   -> __IMPOSSIBLE__	-- not allowed here

-- | Type check a bunch of mutual inductive recursive definitions.
checkMutual :: DeclInfo -> [A.TypeSignature] -> [A.Definition] -> TCM ()
checkMutual i ts ds = do
  mapM_ checkTypeSignature ts
  mapM_ checkDefinition ds
  whenM positivityCheckEnabled $
      checkStrictlyPositive [ name | A.DataDef _ name _ _ <- ds ]


-- | Type check the type signature of an inductive or recursive definition.
checkTypeSignature :: A.TypeSignature -> TCM ()
checkTypeSignature (A.ScopedDecl scope ds) = do
  setScope scope
  mapM_ checkTypeSignature ds
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
	A.RecDef i x ps cs  -> abstract (defAbstract i) $ checkRecDef i x ps cs
    where
	-- Concrete definitions cannot use information about abstract things.
	abstract ConcreteDef = inAbstractMode
	abstract _	     = id


-- | Type check a module.
checkSection :: ModuleInfo -> ModuleName -> A.Telescope -> [A.Declaration] -> TCM ()
checkSection i x tel ds =
  checkTelescope tel $ \tel' -> do
    addSection x (size tel')
    verbose 10 $ do
      dx   <- prettyTCM x
      dtel <- mapM prettyA tel
      dtel' <- prettyTCM =<< lookupSection x
      liftIO $ putStrLn $ "checking section " ++ show dx ++ " " ++ show dtel
      liftIO $ putStrLn $ "    actual tele: " ++ show dtel'
    withCurrentModule x $ checkDecls ds
    exitSection x

-- | Check an application of a section.
checkSectionApplication ::
  ModuleInfo -> ModuleName -> ModuleName -> [NamedArg A.Expr] ->
  Map QName QName -> Map ModuleName ModuleName -> TCM ()
checkSectionApplication i m1 m2 args rd rm = do
  tel <- lookupSection m2
  vs  <- freeVarsToApply $ qnameFromList $ mnameToList m2
  verbose 15 $ do
    dm2	 <- prettyTCM m2
    dtel <- prettyTCM tel
    liftIO $ putStrLn $ "applying section " ++ show dm2
    liftIO $ putStrLn $ "  tel = " ++ show dtel
  (ts, cs)  <- checkArguments_ (getRange i) args (apply tel vs)
  noConstraints $ return cs
  verbose 15 $ do
    [d1,d2] <- mapM prettyTCM [m1,m2]
    dts	    <- mapM prettyTCM (vs ++ ts)
    liftIO $ putStrLn $ unwords [ "applySection", show d1, "=", show d2, show dts ]
    liftIO $ putStrLn $ "  defs: " ++ show rd
    liftIO $ putStrLn $ "  mods: " ++ show rm
  applySection m1 m2 (vs ++ ts) rd rm

-- | Type check an import declaration. Actually doesn't do anything, since all
--   the work is done when scope checking.
checkImport :: ModuleInfo -> ModuleName -> TCM ()
checkImport i x = return ()

---------------------------------------------------------------------------
-- * Datatypes
---------------------------------------------------------------------------

-- | Type check a datatype definition. Assumes that the type has already been
--   checked.
checkDataDef :: DefInfo -> QName -> [A.LamBinding] -> [A.Constructor] -> TCM ()
checkDataDef i name ps cs =
    traceCall (CheckDataDef (getRange i) (qnameName name) ps cs) $ do -- TODO!! (qnameName)
	let npars = size ps

	-- Look up the type of the datatype.
	t <- typeOfConst name

	-- The parameters are in scope when checking the constructors. 
	(nofIxs, s) <- bindParameters ps t $ \tel t0 -> do

	    -- Parameters are always hidden in constructors
	    let tel' = hideTel tel

	    -- The type we get from bindParameters is Θ -> s where Θ is the type of
	    -- the indices. We count the number of indices and return s.
	    (nofIxs, s) <- splitType =<< normalise t0

	    -- Change the datatype from an axiom to a datatype with no constructors.
	    escapeContext (size tel) $
	      addConstant name (Defn name t $ Datatype npars nofIxs Nothing []
						       s (defAbstract i)
			       )

	    -- Check the types of the constructors
	    mapM_ (checkConstructor name tel' nofIxs s) cs

	    -- Return the target sort and the number of indices
	    return (nofIxs, s)

	-- If proof irrelevance is enabled we have to check that datatypes in
	-- Prop contain at most one element.
	do  proofIrr <- proofIrrelevance
	    case (proofIrr, s, cs) of
		(True, Prop, _:_:_) -> typeError PropMustBeSingleton
		_		    -> return ()

	-- Add the datatype to the signature as a datatype. It was previously
	-- added as an axiom.
	addConstant name (Defn name t $ Datatype npars nofIxs Nothing (map cname cs)
						 s (defAbstract i)
			 )
    where
	cname (A.ScopedDecl _ [d]) = cname d
	cname (A.Axiom _ x _)	   = x
	cname _			   = __IMPOSSIBLE__ -- constructors are axioms

	hideTel  EmptyTel		  = EmptyTel
	hideTel (ExtendTel (Arg _ t) tel) = ExtendTel (Arg Hidden t) $ hideTel <$> tel

	splitType (El _ (Pi _ b))  = ((+ 1) -*- id) <$> splitType (absBody b)
	splitType (El _ (Fun _ b)) = ((+ 1) -*- id) <$> splitType b
	splitType (El _ (Sort s))  = return (0, s)
	splitType (El _ t)	   = typeError $ DataMustEndInSort t

-- | Type check a constructor declaration. Checks that the constructor targets
--   the datatype and that it fits inside the declared sort.
checkConstructor :: QName -> Telescope -> Int -> Sort -> A.Constructor -> TCM ()
checkConstructor d tel nofIxs s (A.ScopedDecl scope [con]) = do
  setScope scope
  checkConstructor d tel nofIxs s con
checkConstructor d tel nofIxs s con@(A.Axiom i c e) =
    traceCall (CheckConstructor d tel s con) $ do
	t <- isType_ e
	n <- size <$> getContextTelescope
	verbose 5 $ do
	    td <- prettyTCM t
	    liftIO $ putStrLn $ "checking that " ++ show td ++ " ends in " ++ show d
	    liftIO $ putStrLn $ "  nofPars = " ++ show n
	constructs n t d
	verbose 5 $ do
	    d <- prettyTCM s
	    liftIO $ putStrLn $ "checking that the type fits in " ++ show d
	t `fitsIn` s
	escapeContext (size tel)
	    $ addConstant c
	    $ Defn c (telePi tel t) $ Constructor (size tel) c d $ defAbstract i
checkConstructor _ _ _ _ _ = __IMPOSSIBLE__ -- constructors are axioms


-- | Bind the parameters of a datatype. The bindings should be domain free.
bindParameters :: [A.LamBinding] -> Type -> (Telescope -> Type -> TCM a) -> TCM a
bindParameters [] a ret = ret EmptyTel a
bindParameters (A.DomainFree h x : ps) (El _ (Pi (Arg h' a) b)) ret	-- always dependent function
    | h /= h'	=
	__IMPOSSIBLE__
    | otherwise = addCtx x arg $ bindParameters ps (absBody b) $ \tel s ->
		    ret (ExtendTel arg $ Abs (show x) tel) s
  where
    arg = Arg h a
bindParameters _ _ _ = __IMPOSSIBLE__


-- | Check that the arguments to a constructor fits inside the sort of the datatype.
--   The first argument is the type of the constructor.
fitsIn :: Type -> Sort -> TCM ()
fitsIn t s =
    do	t <- instantiate t
	case funView $ unEl t of
	    FunV arg@(Arg h a) _ -> do
		let s' = getSort a
		s' `leqSort` s
		x <- freshName_ (argName t)
		let v  = Arg h $ Var 0 []
		    t' = piApply (raise 1 t) [v]
		addCtx x arg $ fitsIn t' s
	    _		     -> return ()

-- | Check that a type constructs something of the given datatype. The first
--   argument is the number of parameters to the datatype.
--   TODO: what if there's a meta here?
constructs :: Int -> Type -> QName -> TCM ()
constructs nofPars t q = constrT 0 t
    where
	constrT n (El s v) = constr n s v

	constr n s v = do
	    v <- reduce v
	    case v of
		Pi a b	-> underAbstraction a b $ \t ->
			   constrT (n + 1) t
		Fun _ b -> constrT n b
		Def d vs
		    | d == q -> checkParams n =<< reduce (take nofPars vs)
						    -- we only check the parameters
		_ -> bad $ El s v

	bad t = typeError $ ShouldEndInApplicationOfTheDatatype t

	checkParams n vs = zipWithM_ sameVar (map unArg vs) ps
	    where
		def = Def q []
		ps = reverse [ i | (i,Arg h _) <- zip [n..] vs ]

		sameVar v i = do
		    t <- typeOfBV i
		    noConstraints $ equalTerm t v (Var i [])


-- | Get the canonical datatype (i.e. the defining datatype) for a given name.
--   The name should be a datatype, but it can be a redefined datatype.
canonicalDatatype :: MonadTCM tcm => QName -> tcm QName
canonicalDatatype d = do
  Datatype _ _ cl _ _ _ <- theDef <$> getConstInfo d
  case cl of
    Nothing	      -> return d
    Just (Clause _ v) -> canonicalDatatype $ bodyName v
  where
    bodyName (Bind b)	= bodyName $ absBody b
    bodyName (NoBind b) = bodyName b
    bodyName (Body v)	= name v
    bodyName  NoBody	= __IMPOSSIBLE__
    name (Lam _ b) = name $ absBody b
    name (Def d _) = d
    name _	   = __IMPOSSIBLE__

-- | Force a type to be a specific datatype.
forceData :: MonadTCM tcm => QName -> Type -> tcm Type
forceData d (El s0 t) = liftTCM $ do
    t' <- reduce t
    d <- canonicalDatatype d
    case t' of
	Def d' _
	    | d == d'   -> return $ El s0 t'
	    | otherwise	-> fail $ "wrong datatype " ++ show d ++ " != " ++ show d'
	MetaV m vs	    -> do
	    Defn _ t (Datatype _ _ _ _ s _) <- getConstInfo d
	    ps <- newArgsMeta t
	    noConstraints $ equalType (El s0 t') (El s (Def d ps)) -- TODO: too strict?
	    reduce $ El s0 t'
	_ -> typeError $ ShouldBeApplicationOf (El s0 t) d

---------------------------------------------------------------------------
-- * Records
---------------------------------------------------------------------------

checkRecDef :: DefInfo -> QName -> [A.LamBinding] -> [A.Constructor] -> TCM ()
checkRecDef i name ps fields =
  traceCall (CheckRecDef (getRange i) (qnameName name) ps fields) $ do
    t <- instantiateFull =<< typeOfConst name
    bindParameters ps t $ \tel t0 -> do
      s <- case unEl t0 of
	Sort s	-> return s
	_	-> typeError $ ShouldBeASort t0
      let m = mnameFromList $ qnameToList name
	  hide (Arg _ x) = Arg Hidden x
	  htel		 = map hide $ telToList tel
	  rect		 = El s $ Def name $ reverse 
			   [ Arg h (Var i [])
			   | (i, Arg h _) <- zip [0..] $ telToList tel
			   ]
	  tel'		 = telFromList $ htel ++ [Arg NotHidden ("r", rect)]

      -- We have to rebind the parameters to make them hidden
      escapeContext (size tel) $ addCtxTel tel' $ addSection m (size tel')

      -- Check the types of the fields
      ftel <- withCurrentModule m $ checkRecordFields m name tel s [] [] (size fields) fields

      -- Exit the section (set the number of free vars to 0)
      exitSection m

      -- Check that the fields fit inside the sort
      telePi ftel t0 `fitsIn` s

      let getName (A.Axiom _ x _)      = x
	  getName (A.ScopedDecl _ [f]) = getName f
	  getName _		       = __IMPOSSIBLE__
      addConstant name $ Defn name t0
		       $ Record (size tel) Nothing
				(map getName fields) ftel s
				(defAbstract i)
      return ()

{-| @checkRecordFields m q tel s ftel vs n fs@:
    @m@: name of the generated module
    @q@: name of the record
    @tel@: parameters
    @s@: sort of the record
    @ftel@: telescope of previous fields
    @vs@: values of previous fields (should have one free variable, which is
	  the record)
    @n@: total number of fields
    @fs@: the fields to be checked
-}
checkRecordFields :: ModuleName -> QName -> Telescope -> Sort ->
		     [(Name, Type)] -> [Term] -> Arity -> [A.Field] ->
		     TCM Telescope
checkRecordFields m q tel s ftel vs n [] = return EmptyTel
checkRecordFields m q tel s ftel vs n (f : fs) = do
  (x, a, v) <- checkField f
  let ftel' = ftel ++ [(x, a)]
  tel <- checkRecordFields m q tel s ftel' (v : vs) n fs
  return $ Arg NotHidden a `ExtendTel` Abs (show x) tel
  where
    checkField :: A.Field -> TCM (Name, Type, Term)
    checkField (A.ScopedDecl scope [f]) =
      setScope scope >> checkField f
    checkField (A.Axiom i x t) = do
      -- check the type (in the context of the telescope)
      -- the previous fields will be free in 
      verbose 5 $ do
	top <- prettyTCM =<< getContextTelescope
	dtel <- prettyTCM tel
	dftel1 <- mapM (prettyTCM . fst) ftel
	dftel2 <- mapM (prettyTCM . snd) ftel
	dvs    <- mapM prettyTCM vs
	let dftel = zip dftel1 dftel2
	dt    <- prettyA t
	liftIO $ putStrLn $ unlines
	  [ "top  = " ++ show top
	  , "tel  = " ++ show dtel
	  , "ftel = " ++ show dftel
	  , "t    = " ++ show dt
	  , "vs   = " ++ show dvs
	  ]
      let add (x, t) = addCtx x (Arg NotHidden t)
      t <- flip (foldr add) ftel $ isType_ t
      -- create the projection functions (instantiate the type with the values
      -- of the previous fields)

      {- what are the contexts?

	  tel, ftel    ⊢ t
	  tel, r       ⊢ vs
	  tel, r, ftel ⊢ raiseFrom (size ftel) 1 t
	  tel, r       ⊢ substs vs (raiseFrom (size ftel) 1 t)
      -}

      -- The type of the projection function should be
      -- {tel} -> (r : R tel) -> t[vs/ftel]
      let hide (Arg _ x) = Arg Hidden x
	  htel	   = telFromList $ map hide $ telToList tel
	  rect	   = El s $ Def q $ reverse 
		      [ Arg h (Var i [])
		      | (i, Arg h _) <- zip [0..] $ telToList tel
		      ]
	  projt	   = substs (vs ++ map (flip Var []) [0..]) $ raiseFrom (size ftel) 1 t
	  finalt   = telePi htel
		   $ telePi (ExtendTel (Arg NotHidden rect) (Abs "r" EmptyTel))
		   $ projt
	  projname = qualify m $ qnameName x
      
      -- The body should be
      --  P.xi {tel} (r _ .. x .. _) = x
      let hps	 = map (fmap $ VarP . fst) $ telToList htel
	  conp	 = Arg NotHidden
		 $ ConP q $ map (Arg NotHidden)
			    [ VarP "x" | _ <- [1..n] ]
	  nobind 0 = id
	  nobind n = NoBind . nobind (n - 1)
	  body	 = nobind (size htel)
		 $ nobind (size ftel)
		 $ Bind . Abs "x"
		 $ nobind (n - size ftel - 1)
		 $ Body $ Var 0 []
	  clause = Clause (hps ++ [conp]) body
      escapeContext (size tel) $
	addConstant projname (Defn projname finalt $ Function [clause] ConcreteDef)

      -- The value of the projection is the projection function applied
      -- to the parameters and the record (these are free in the value)
      let projval = Def projname $
		    reverse [ let h = if i == 0
				      then NotHidden
				      else Hidden
			      in Arg h (Var i [])
			    | i <- [0 .. size tel]
			    ]

      return (qnameName projname, t, projval)
    checkField _ = __IMPOSSIBLE__ -- record fields are always axioms

---------------------------------------------------------------------------
-- * Definitions by pattern matching
---------------------------------------------------------------------------

-- | Type check a definition by pattern matching.
checkFunDef :: DefInfo -> QName -> [A.Clause] -> TCM ()
checkFunDef i name cs =

    traceCall (CheckFunDef (getRange i) (qnameName name) cs) $ do   -- TODO!! (qnameName)
	-- Get the type of the function
	t    <- typeOfConst name

	-- Check the clauses
	cs <- mapM (checkClause t) cs

	-- Check that all clauses have the same number of arguments
	unless (allEqual $ map npats cs) $ typeError DifferentArities

	-- Annotate the clauses with which arguments are actually used.
	cs <- mapM rebindClause cs

	-- Add the definition
	addConstant name $ Defn name t $ Function cs $ defAbstract i
	verbose 10 $ do
	  dx <- prettyTCM name
	  t' <- prettyTCM . defType =<< getConstInfo name
	  liftIO $ putStrLn $ "added " ++ show dx ++ " : " ++ show t'
    where
	npats (Clause ps _) = size ps


-- | Type check a function clause.
checkClause :: Type -> A.Clause -> TCM Clause
checkClause t c@(A.Clause (A.LHS i x aps) rhs wh) =
    traceCall (CheckClause t c) $
    checkLHS aps t $ \sub xs ps t' -> do
      body <- checkWhere (size xs) wh $ 
	      case rhs of
		A.RHS e -> do
		  v <- checkExpr e t'
		  return $ foldr (\x t -> Bind $ Abs x t) (Body $ substs sub v) xs
		A.AbsurdRHS
		  | any (containsAbsurdPattern . namedThing . unArg) aps
			      -> return NoBody
		  | otherwise -> typeError $ NoRHSRequiresAbsurdPattern aps
      return $ Clause ps body

-- | Type check a where clause. The first argument is the number of variables
--   bound in the left hand side.
checkWhere :: Int -> [A.Declaration] -> TCM a -> TCM a
checkWhere _ []			     ret = ret
checkWhere n [A.ScopedDecl scope ds] ret = setScope scope >> checkWhere n ds ret
checkWhere n [A.Section _ m tel ds]  ret = do
  checkTelescope tel $ \tel' -> do
    addSection m (size tel' + n)  -- the variables bound in the lhs
				  -- are also parameters
    verbose 10 $ do
      dx   <- prettyTCM m
      dtel <- mapM prettyA tel
      dtel' <- prettyTCM =<< lookupSection m
      liftIO $ putStrLn $ "checking where section " ++ show dx ++ " " ++ show dtel
      liftIO $ putStrLn $ "	   actual tele: " ++ show dtel'
    x <- withCurrentModule m $ checkDecls ds >> ret
    exitSection m
    return x
checkWhere _ _ _ = __IMPOSSIBLE__

-- | Check if a pattern contains an absurd pattern. For instance, @suc ()@
containsAbsurdPattern :: A.Pattern -> Bool
containsAbsurdPattern p = case p of
    A.AbsurdP _   -> True
    A.VarP _	  -> False
    A.WildP _	  -> False
    A.ImplicitP _ -> False
    A.DotP _ _	  -> False
    A.LitP _	  -> False
    A.AsP _ _ p   -> containsAbsurdPattern p
    A.ConP _ _ ps -> any (containsAbsurdPattern . namedThing . unArg) ps
    A.DefP _ _ _  -> __IMPOSSIBLE__

-- | Type check a left-hand side.
checkLHS :: [NamedArg A.Pattern] -> Type -> ([Term] -> [String] -> [Arg Pattern] -> Type -> TCM a) -> TCM a
checkLHS ps t ret = do

    verbose 15 $ do
      dt  <- prettyTCM t
      dps <- mapM prettyA ps
      liftIO $ putStrLn $ "checking clause " ++ show dps ++ " : " ++ show dt

    -- Save the state for later. (should this be done with the undo monad, or
    -- would that interfere with normal undo?)
    rollback <- do
	st  <- get
	env <- ask
	return $ \k -> do put st; local (const env) k

    -- Preliminary type checking to decide what should be variables and what
    -- should be dotted. Ignore empty types.
    runCheckPatM (checkPatterns ps t) $ \xs metas _ (ps0, ps, ts, a) -> do

    -- Build the new pattern, turning implicit patterns into variables when
    -- they couldn't be solved.
    ps1 <- evalStateT (buildNewPatterns ps0) metas

    verbose 10 $ do
	d0 <- A.showA ps0
	d1 <- A.showA ps1
	liftIO $ do
	putStrLn $ "first check"
	putStrLn $ "  xs    = " ++ show xs
	putStrLn $ "  metas = " ++ show metas
	putStrLn $ "  ps0   = " ++ d0
	putStrLn $ "  ps1   = " ++ d1

    verbose 10 $ do
	is <- mapM (instantiateFull . flip MetaV []) metas
	ds <- mapM prettyTCM is
	dts <- mapM prettyTCM =<< mapM instantiateFull ts
	liftIO $ putStrLn $ "  is    = " ++ concat (List.intersperse ", " $ map show ds)
	liftIO $ putStrLn $ "  ts    = " ++ concat (List.intersperse ", " $ map show dts)

    -- Now we forget that we ever type checked anything and type check the new
    -- pattern.
    rollback $ runCheckPatM (checkPatterns ps1 t)
	     $ \xs metas emptyTypes (_, ps, ts, a) -> do

    -- Check that the empty types are indeed empty
    mapM_ isEmptyType emptyTypes

    verbose 10 $ liftIO $ do
	putStrLn $ "second check"
	putStrLn $ "  xs    = " ++ show xs
	putStrLn $ "  metas = " ++ show metas

    verbose 10 $ do
	is <- mapM (instantiateFull . flip MetaV []) metas
	ds <- mapM prettyTCM is
	liftIO $ putStrLn $ "  is    = " ++ concat (List.intersperse ", " $ map show ds)

    -- Finally we type check the dot patterns and check that they match their
    -- instantiations.
    evalStateT (checkDotPatterns ps1) metas

    -- Sanity check. Make sure that all metas were instantiated.
    is <- mapM lookupMeta metas
    case [ getRange i | i <- is, FirstOrder <- [mvInstantiation i] ] of
	[] -> return ()
	rs -> fail $ "unsolved pattern metas at\n" ++ unlines (map show rs)

    -- Make sure to purge the type and the context from any first-order metas.
    a	 <- instantiateFull a
    flat <- instantiateFull =<< flatContext

    -- The context might not be well-formed. We may have to do some reordering.
    reportLn 20 $ "Before reordering:"
    verbose 20 $ dumpContext flat

    flat' <- reorderCtx flat

    -- Compute renamings to and from the new context
    let sub  = (computeSubst `on` map (fst . unArg)) flat flat'
	rsub = (computeSubst `on` map (fst . unArg)) flat' flat

    -- Apply the reordering to the types in the new context
    let flat'' = map (fmap $ id -*- substs sub) flat'

    reportLn 20 $ "After reordering:"
    verbose 20 $ dumpContext flat'

    -- Deflatten the context
    let ctx = mkContext flat''

    inContext ctx $ do

	verbose 20 $ do
	    d <- prettyTCM ctx
	    dt <- prettyTCM (substs sub a)
	    liftIO $ putStrLn $ "context = " ++ show d
	    liftIO $ putStrLn $ "type    = " ++ show dt

	reportLn 20 $ "finished type checking left hand side"
	ret rsub xs ps (substs sub a)
    where
	popMeta = do
	    x : xs <- get
	    put xs
	    return x

	buildNewPatterns :: [NamedArg A.Pattern] -> StateT [MetaId] TCM [NamedArg A.Pattern]
	buildNewPatterns = mapM buildNewPattern'

	buildNewPattern' = (traverse . traverse) buildNewPattern

	buildNewPattern :: A.Pattern -> StateT [MetaId] TCM A.Pattern
	buildNewPattern (A.ImplicitP i) = do
	    x <- popMeta
	    v <- lift $ instantiate (MetaV x [])
	    lift $ verbose 6 $ do
		d <- prettyTCM v
		liftIO $ putStrLn $ "new pattern for " ++ show x ++ " = " ++ show d
	    case v of
		-- Unsolved metas become variables
		MetaV y _ | x == y  -> return $ A.WildP i
		-- Anything else becomes dotted
		_		    -> do
		    lift $ verbose 6 $ do
			d <- prettyTCM =<< instantiateFull v
			liftIO $ putStrLn $ show x ++ " := " ++ show d
		    scope <- lift getScope
		    return $ A.DotP i (A.Underscore $ info scope)
		    where info s = MetaInfo (getRange i) s Nothing

	buildNewPattern p@(A.VarP _)	= return p
	buildNewPattern p@(A.WildP _)	= return p
	buildNewPattern p@(A.DotP _ _)	= popMeta >> return p
	buildNewPattern (A.AsP i x p)	= A.AsP i x <$> buildNewPattern p
	buildNewPattern (A.ConP i c ps) = A.ConP i c <$> buildNewPatterns ps
	buildNewPattern (A.DefP i c ps) = A.DefP i c <$> buildNewPatterns ps
	buildNewPattern p@(A.AbsurdP _)	= return p
	buildNewPattern p@(A.LitP _)	= return p

	checkDotPatterns :: [NamedArg A.Pattern] -> StateT [MetaId] TCM ()
	checkDotPatterns = mapM_ checkDotPattern'

	checkDotPattern' p = (traverse . traverse) checkDotPattern p >> return ()

	checkDotPattern :: A.Pattern -> StateT [MetaId] TCM ()
	checkDotPattern (A.ImplicitP i) = __IMPOSSIBLE__    -- there should be no implicits left at this point
	checkDotPattern p@(A.VarP _)	= return ()
	checkDotPattern p@(A.WildP _)	= return ()
	checkDotPattern p@(A.DotP i e)	= do
	    x <- popMeta
	    lift $ do
		firstOrder <- isFirstOrder x    -- first order and uninstantiated
		when firstOrder $ typeError
				$ InternalError	-- TODO: proper error
				$ "uninstantiated dot pattern at " ++ show (getRange i)
		HasType _ ot <- mvJudgement <$> lookupMeta x
		t <- getOpen ot
		v <- checkExpr e t
		noConstraints $ equalTerm t v (MetaV x [])
	checkDotPattern (A.AsP i x p)	= checkDotPattern p
	checkDotPattern (A.ConP i c ps) = checkDotPatterns ps
	checkDotPattern (A.DefP i c ps) = checkDotPatterns ps
	checkDotPattern p@(A.AbsurdP _)	= return ()
	checkDotPattern p@(A.LitP _)	= return ()

	-- Get the flattened context
	flatContext :: TCM Context
	flatContext = do
	    n <- size <$> getContext
	    mapM f [0..n - 1]
	    where
		f i = do
		    Arg h t <- instantiateFull =<< typeOfBV' i
		    x <- nameOfBV i
		    return $ Arg h (x, t)

	-- Reorder a flat context to make sure it's valid.
	reorderCtx :: Context -> TCM Context
	reorderCtx ctx = reverse <$> reorder (reverse ctx)
	    where
		free t = mapM nameOfBV (Set.toList $ allVars $ freeVars t)

		reorder :: [Arg (Name, Type)] -> TCM [Arg (Name, Type)]
		reorder []	      = return []
		reorder (Arg h (x,t) : tel) = do
		    tel' <- reorder tel
		    xs   <- free t
		    verbose 20 $ do
			d <- prettyTCM t
			liftIO $ putStrLn $ "freeIn " ++ show x ++ " : " ++ show d ++ " are " ++ show xs
		    case List.intersect (map (fst . unArg) tel') xs of
			[] -> return $ Arg h (x,t) : tel'
			zs -> return $ ins zs (Arg h (x,t)) tel'

		ins [] p tel		   = p : tel
		ins xs p (Arg h (x,t):tel) = Arg h (x,t) : ins (List.delete x xs) p tel
		ins (_:_) _ []		   = __IMPOSSIBLE__

	-- Compute a renaming from the first names to the second.
	computeSubst :: [Name] -> [Name] -> [Term]
	computeSubst old new = map ix old
	    where
		ix x = case List.findIndex (==x) new of
			Just i	-> Var i []
			Nothing	-> __IMPOSSIBLE__

	-- Take a flat (but valid) context and turn it into a proper context.
	mkContext :: [Arg (Name, Type)] -> Context
	mkContext = reverse . mkCtx . reverse
	    where
		mkCtx []	  = []
		mkCtx ctx0@(Arg h (x,t) : ctx) = Arg h (x, substs sub t) : mkCtx ctx
		    where
			sub = map err ctx0 ++ [ Var i [] | i <- [0..] ]

			err (Arg _ (y,_)) = error $ show y ++ " occurs in the type of " ++ show x

	-- Print a flat context
	dumpContext :: Context -> TCM ()
	dumpContext ctx = do
	    let pr (Arg h (x,t)) = do
		  d <- prettyTCM t
		  return $ "  " ++ par h (show x ++ " : " ++ show d)
		par Hidden    s = "{" ++ s ++ "}"
		par NotHidden s = "(" ++ s ++ ")"
	    ds <- mapM pr ctx
	    liftIO $ putStr $ unlines $ reverse ds

-- | Check the patterns of a left-hand-side. Binds the variables of the pattern.
checkPatterns :: [NamedArg A.Pattern] -> Type -> CheckPatM r ([NamedArg A.Pattern], [Arg Pattern], [Arg Term], Type)
checkPatterns [] t = do
    -- traceCallCPS (CheckPatterns [] t) ret $ \ret -> do
    t' <- instantiate t
    case funView $ unEl t' of
	FunV (Arg Hidden _) _   -> do
	    r <- getCurrentRange
	    checkPatterns [Arg Hidden $ unnamed $ A.ImplicitP $ PatRange r] t'
	_ -> return ([], [], [], t)

checkPatterns ps0@(Arg h np:ps) t = do
    -- traceCallCPS (CheckPatterns ps0 t) ret $ \ret -> do

    -- Make sure the type is a function type
    (t', cs) <- forcePi h (name np) t
    opent'   <- makeOpen t'

    -- Add any resulting constraints to the global constraint set
    addNewConstraints cs

    -- If np is named then np = {x = p'}
    let p' = namedThing np

    -- We might have to insert wildcards for implicit arguments
    case funView $ unEl t' of

	-- There is a hidden argument missing here (either because the next
	-- pattern is non-hidden, or it's a named hidden pattern with the wrong name).
	-- Insert a {_} and re-type check.
	FunV (Arg Hidden _) _
	    | h == NotHidden ||
	      not (sameName (nameOf np) (nameInPi $ unEl t')) ->
	    checkPatterns (Arg Hidden (unnamed $ A.ImplicitP $ PatRange $ getRange np) : Arg h np : ps) t'

	-- No missing arguments.
	FunV (Arg h' a) _ | h == h' -> do

	    -- Check the first pattern
	    (p0, p, v) <- checkPattern h (argName t') p' a
	    openv      <- makeOpen v

	    -- We're now in an extended context so we have lift t' accordingly.
	    t0 <- getOpen opent'

	    -- Check the rest of the patterns. If the type of all the patterns were
	    -- (x : A)Δ, then we check the rest against Δ[v] where v is the
	    -- value of the first pattern (piApply (Γ -> B) vs == B[vs/Γ]).
	    (ps0, ps, vs, t'') <- checkPatterns ps (piApply t0 [Arg h' v])

	    -- Additional variables have been added to the context.
	    v' <- getOpen openv

	    -- Combine the results
	    return (Arg h (fmap (const p0) np) : ps0, Arg h p : ps, Arg h v':vs, t'')

	_ -> typeError $ WrongHidingInLHS t'
    where
	name (Named _ (A.VarP x)) = show x
	name (Named (Just x) _)   = x
	name _			  = "x"

	sameName Nothing _  = True
	sameName n1	 n2 = n1 == n2

	nameInPi (Pi _ b)  = Just $ absName b
	nameInPi (Fun _ _) = Nothing
	nameInPi _	   = __IMPOSSIBLE__

-- | TODO: move
argName = argN . unEl
    where
	argN (Pi _ b)  = "_" ++ absName b
	argN (Fun _ _) = "_"
	argN _	  = __IMPOSSIBLE__


actualConstructor :: MonadTCM tcm => QName -> tcm QName
actualConstructor c = do
    v <- constructorForm =<< normalise (Con c [])
    case ignoreBlocking v of
	Con c _	-> return c
	_	-> actualConstructor =<< stripLambdas v
    where
	stripLambdas v = case ignoreBlocking v of
	    Con c _ -> return c
	    Lam h b -> do
		x <- freshName_ $ absName b
		addCtx x (Arg h $ sort Prop) $ stripLambdas (absBody b)
	    _	    -> typeError $ GenericError $ "Not a constructor: " ++ show c

-- | Type check a pattern and bind the variables. First argument is a name
--   suggestion for wildcard patterns.
checkPattern :: Hiding -> String -> A.Pattern -> Type -> CheckPatM r (A.Pattern, Pattern, Term)
checkPattern h name p t =
--    traceCallCPS (CheckPattern name p t) ret $ \ret -> case p of
    case p of

	-- Variable. Simply bind the variable.
	A.VarP x    -> do
	    bindPatternVar x (Arg h t)
	    return (p, VarP (show x), Var 0 [])

	-- Wild card. Create and bind a fresh name.
	A.WildP i   -> do
	    x <- freshName (getRange i) name
	    bindPatternVar x (Arg h t)
	    return (p, VarP name, Var 0 [])

	-- Implicit pattern. Create a new meta variable.
	A.ImplicitP i -> do
	    x <- addPatternMeta normalMetaPriority t
	    return (p, WildP, MetaV x [])

	-- Dot pattern. Create a meta variable.
	A.DotP i _ -> do
	    -- we should always instantiate dotted patterns first
	    x <- addPatternMeta highMetaPriority t
	    return (p, WildP, MetaV x [])

	-- Constructor. This is where the action is.
	A.ConP i c ps -> do

	    -- We're gonna need t in a different context so record the current
	    -- one.
	    ot <- makeOpen t

-- 	    (t', vs) <- do
-- 		-- Get the type of the constructor and the target datatype. The
-- 		-- type is the full lambda lifted type.
-- 		Defn _ t' (Constructor _ _ d _) <- getConstInfo c
-- 
-- 		-- Make sure that t is an application of the datatype to its
-- 		-- parameters (and some indices). This will include module
-- 		-- parameters.
-- 		Def d' _ <- reduce (Def d [])
-- 
-- 		verbose 10 $ do
-- 		  t <- prettyTCM t
-- 		  liftIO $ putStrLn $ "checking constructor " ++ show c ++
-- 				" of type " ++ show d ++ " (" ++ show d' ++ ")"
-- 		  liftIO $ putStrLn $ "  against type " ++ show t
-- 		  
-- 
-- 		El _ (Def _ vs)	<- forceData d' t
-- 
-- 		-- Get the number of parameters of the datatype, including
-- 		-- parameters to enclosing modules.
-- 		Datatype nofPars _ _ _ _ _ <- theDef <$> getConstInfo d
-- 
-- 		-- Throw away the indices
-- 		let vs' = take nofPars vs
-- 		return (t', vs')
-- 
-- 	    -- Compute the canonical form of the constructor (it might go
-- 	    -- through a lot of module instantiations).
-- 	    Con c' [] <- constructorForm =<< reduce (Con c [])

	    -- Infer the type of the constructor
	    (_, a) <- liftTCM $ inferDef Con c

	    Constructor n _ _ _ <- theDef <$> (instantiateDef =<< getConstInfo c)

	    liftTCM $ verbose 20 $ do
	      da  <- prettyTCM a
	      pds <- mapM pretty =<< mapM abstractToConcrete_ ps
	      liftIO $ putStrLn $ "checking pattern " ++ show c ++ " " ++ show pds
		      ++ "\n  type         " ++ show da
		      ++ "\n  nof pars     " ++ show n

	    -- Create meta variables for the parameters
	    a' <- let createMetas 0 a = return a
		      createMetas n a = do
			a <- reduce a
			case funView $ unEl a of
			  FunV (Arg h b) _ -> do
			    m <- newValueMeta b
			    createMetas (n - 1) (a `piApply` [Arg h m])
			  _   -> do
			    d <- prettyTCM a
			    fail $ show d ++ " should have had " ++ show n ++ " more arguments"
			    __IMPOSSIBLE__
		  in  createMetas n a

	    liftTCM $ verbose 20 $ do
	      da' <- prettyTCM a'
	      liftIO $ putStrLn $ "  instantiated " ++ show da'


	    -- Check the arguments against that type
	    (aps, ps', ts', rest) <- checkPatterns ps a' -- (piApply t' vs)

	    -- Compute the corresponding value (possibly blocked by constraints)
	    v <- do
		tn  <- getOpen ot
		blockTerm tn (Con c ts') $ equalType rest tn

	    -- Get the canonical name for the constructor
	    Constructor _ c' _ _ <- theDef <$> getConstInfo c

	    return (A.ConP i c' aps, ConP c' ps', v)
	    where
		hide (Arg _ x) = Arg Hidden x

	-- Absurd pattern. Make sure that the type is empty. Otherwise treat as
	-- an anonymous variable.
	A.AbsurdP i -> do
	    thisTypeShouldBeEmpty t
	    x <- freshName (getRange i) name
	    bindPatternVar x (Arg h t)
	    return (p, AbsurdP, Var 0 [])

	-- As pattern. Create a let binding for the term corresponding to the
	-- pattern.
	A.AsP i x p -> do
	    ot	       <- makeOpen t
	    (p0, p, v) <- checkPattern h name p t
	    t	       <- getOpen ot
	    verbose 15 $ do
		dt <- prettyTCM t
		dv <- prettyTCM v
		dctx <- prettyTCM =<< getContext
		liftIO $ putStrLn $ show dctx ++ " |-"
		liftIO $ putStrLn $ "  " ++ show x ++ " : " ++ show dt
		liftIO $ putStrLn $ "  " ++ show x ++ " = " ++ show dv
	    liftPatCPS_ (addLetBinding x v t)
	    return (A.AsP i x p0, p, v)

	-- Literal.
	A.LitP l    -> do
	    v <- liftTCM $ checkLiteral l t
	    return (p, LitP l, v)

	-- Defined patterns are not implemented.
	A.DefP i f ps ->
	    typeError $ NotImplemented "defined patterns"


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
forcePi :: MonadTCM tcm => Hiding -> String -> Type -> tcm (Type, Constraints)
forcePi h name (El s t) =
    do	t' <- reduce t
	case t' of
	    Pi _ _	-> return (El s t', [])
	    Fun _ _	-> return (El s t', [])
            _           -> do
                sa <- newSortMeta
                sb <- newSortMeta
                let s' = sLub sa sb

                a <- newTypeMeta sa
                x <- freshName_ name
		let arg = Arg h a
                b <- addCtx x arg $ newTypeMeta sb
                let ty = El s' $ Pi arg (Abs (show x) b)
                cs <- equalType (El s t') ty
                ty' <- reduce ty
                return (ty', cs)


---------------------------------------------------------------------------
-- * Telescopes
---------------------------------------------------------------------------

-- | Type check a telescope. Binds the variables defined by the telescope.
checkTelescope :: A.Telescope -> (Telescope -> TCM a) -> TCM a
checkTelescope [] ret = ret EmptyTel
checkTelescope (b : tel) ret =
    checkTypedBindings b $ \tel1 ->
    checkTelescope tel   $ \tel2 ->
	ret $ abstract tel1 tel2


-- | Check a typed binding and extends the context with the bound variables.
--   The telescope passed to the continuation is valid in the original context.
checkTypedBindings :: A.TypedBindings -> (Telescope -> TCM a) -> TCM a
checkTypedBindings (A.TypedBindings i h bs) ret =
    thread (checkTypedBinding h) bs $ \bss ->
    ret $ foldr (\(x,t) -> ExtendTel (Arg h t) . Abs x) EmptyTel (concat bss)

checkTypedBinding :: Hiding -> A.TypedBinding -> ([(String,Type)] -> TCM a) -> TCM a
checkTypedBinding h (A.TBind i xs e) ret = do
    t <- isType_ e
    addCtxs xs (Arg h t) $ ret $ mkTel xs t
    where
	mkTel [] t     = []
	mkTel (x:xs) t = (show $ nameConcrete x,t) : mkTel xs (raise 1 t)
checkTypedBinding h (A.TNoBind e) ret = do
    t <- isType_ e
    ret [("_",t)]


---------------------------------------------------------------------------
-- * Terms
---------------------------------------------------------------------------

-- | Type check an expression.
checkExpr :: A.Expr -> Type -> TCM Term
checkExpr e t =
    traceCall (CheckExpr e t) $ do
    verbose 15 $ do
        d <- text "Checking" <+> fsep [ prettyTCM e, text ":", prettyTCM t ]
        liftIO $ print d
    t <- reduce t
    verbose 15 $ do
        d <- text "    --> " <+> prettyTCM t
        liftIO $ print d
    let scopedExpr (A.ScopedExpr scope e) = setScope scope >> scopedExpr e
	scopedExpr e			  = return e
    e <- scopedExpr e
    case e of

	-- Insert hidden lambda if appropriate
	_   | not (hiddenLambda e)
	    , FunV (Arg Hidden _) _ <- funView (unEl t) -> do
		x <- freshName r (argName t)
                reportLn 15 $ "Inserting implicit lambda"
		checkExpr (A.Lam (ExprRange $ getRange e) (A.DomainFree Hidden x) e) t
	    where
		r = emptyR (rStart $ getRange e)
		    where
			emptyR r = Range r r

		hiddenLambda (A.Lam _ (A.DomainFree Hidden _) _)		     = True
		hiddenLambda (A.Lam _ (A.DomainFull (A.TypedBindings _ Hidden _)) _) = True
		hiddenLambda _							     = False

	-- Variable or constant application
	_   | Application hd args <- appView e -> do
		(f,  t0)     <- inferHead hd
		(vs, t1, cs) <- checkArguments (getRange hd) args t0 t
		blockTerm t (f vs) $ (cs ++) <$> equalType t1 t

	A.App i e arg -> do
	    (v0, t0)	 <- inferExpr e
	    (vs, t1, cs) <- checkArguments (getRange e) [arg] t0 t
	    blockTerm t (apply v0 vs) $ (cs ++) <$> equalType t1 t

	A.Lam i (A.DomainFull b) e ->
	    checkTypedBindings b $ \tel -> do
	    t1 <- newTypeMeta_
	    cs <- escapeContext (size tel) $ equalType t (telePi tel t1)
	    v <- checkExpr e t1
	    blockTerm t (teleLam tel v) (return cs)
	    where
		name (Arg h (x,_)) = Arg h x

	A.Lam i (A.DomainFree h x) e0 -> do
	    (t',cs) <- forcePi h (show x) t
	    case funView $ unEl t' of
		FunV arg0@(Arg h' a) _
		    | h == h' ->
			addCtx x arg0 $ do
			let arg = Arg h (Var 0 [])
			    tb  = raise 1 t' `piApply` [arg]
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

	A.Rec _ fs  -> do
	  t <- normalise t
	  case unEl t of
	    Def r vs  -> do
	      xs   <- getRecordFieldNames r
	      ftel <- getRecordFieldTypes r
	      es <- orderFields r xs fs
	      let tel = ftel `apply` vs
	      (args, cs) <- checkArguments_ (getRange e)
			      (map (Arg NotHidden . unnamed) es) tel
	      blockTerm t (Con r args) $ return cs
	    _  -> typeError $ ShouldBeRecordType t

	A.Var _    -> __IMPOSSIBLE__
	A.Def _    -> __IMPOSSIBLE__
	A.Con _    -> __IMPOSSIBLE__

	A.ScopedExpr scope e -> setScope scope >> checkExpr e t

-- | TODO: think this through
{-
nofConstructorPars :: QName -> TCM Int
nofConstructorPars c = do
    Con c' [] <- constructorForm =<< reduce (Con c [])
    nargs     <- constructorArgs c
    nargs'    <- constructorArgs c'
    npars'    <- constructorPars c'
    return $ nargs - (nargs' - npars')
  where
    constructorPars :: QName -> TCM Int
    constructorPars c = do
      c' <- actualConstructor c
      Constructor _ d _	  <- theDef <$> getConstInfo c'
      Datatype np _ _ _ _ <- theDef <$> getConstInfo d
      return np

    constructorArgs :: QName -> TCM Int
    constructorArgs c = do
      t <- defType <$> getConstInfo c
      arity <$> normalise t

    arity :: Type -> Int
    arity t = 
      case unEl t of
	Pi _ (Abs _ b)	-> 1 + arity b
	Fun _ b		-> 1 + arity b
	_		-> 0
-}

-- | Infer the type of a head thing (variable, function symbol, or constructor)
inferHead :: Head -> TCM (Args -> Term, Type)
inferHead (HeadVar x) = do -- traceCall (InferVar x) $ do
  (u, a) <- getVarInfo x
  return (apply u, a)
inferHead (HeadDef x) = do
  (u, a) <- inferDef Def x
  return (apply u, a)
inferHead (HeadCon c) = do

  -- Constructors are polymorphic internally so when building the constructor
  -- term we should throw away arguments corresponding to parameters.

  -- First, inferDef will try to apply the constructor to the free parameters
  -- of the current context. We ignore that.
  (u, a) <- inferDef (\c _ -> Con c []) c

  -- Next get the number of parameters in the current context.
  Constructor n _ _ _ <- theDef <$> (instantiateDef =<< getConstInfo c)

  verbose 7 $ do
    liftIO $ putStrLn $ unwords [show c, "has", show n, "parameters."]

  -- So when applying the constructor throw away the parameters.
  return (apply u . drop n, a)

inferDef :: (QName -> Args -> Term) -> QName -> TCM (Term, Type)
inferDef mkTerm x =
    traceCall (InferDef (getRange x) x) $ do
    d  <- instantiateDef =<< getConstInfo x
    vs <- freeVarsToApply x
    verbose 10 $ do
      ds <- mapM prettyTCM vs
      dx <- prettyTCM x
      dt <- prettyTCM $ defType d
      liftIO $ putStrLn $ "inferred def " ++ unwords (show dx : map show ds) ++ " : " ++ show dt
    return (mkTerm x vs, defType d)


-- | Check a list of arguments: @checkArgs args t0 t1@ checks that
--   @t0 = Delta -> t0'@ and @args : Delta@. Inserts hidden arguments to
--   make this happen. Returns @t0'@ and any constraints that have to be
--   solve for everything to be well-formed.
--   TODO: doesn't do proper blocking of terms
checkArguments :: Range -> [NamedArg A.Expr] -> Type -> Type -> TCM (Args, Type, Constraints)
checkArguments r [] t0 t1 =
    traceCall (CheckArguments r [] t0 t1) $ do
	t0' <- reduce t0
	t1' <- reduce t1
	case funView $ unEl t0' of -- TODO: clean
	    FunV (Arg Hidden a) _ | notHPi $ unEl t1'  -> do
		v  <- newValueMeta a
		let arg = Arg Hidden v
		(vs, t0'',cs) <- checkArguments r [] (piApply t0' [arg]) t1'
		return (arg : vs, t0'',cs)
	    _ -> return ([], t0', [])
    where
	notHPi (Pi  (Arg Hidden _) _) = False
	notHPi (Fun (Arg Hidden _) _) = False
	notHPi _		      = True

checkArguments r args0@(Arg h e : args) t0 t1 =
    traceCall (CheckArguments r args0 t0 t1) $ do
	(t0', cs) <- forcePi h (name e) t0
	e' <- return $ namedThing e
	case (h, funView $ unEl t0') of
	    (NotHidden, FunV (Arg Hidden a) _) -> do
		u  <- newValueMeta a
		let arg = Arg Hidden u
		(us, t0'',cs') <- checkArguments r (Arg h e : args)
				       (piApply t0' [arg]) t1
		return (arg : us, t0'', cs ++ cs')
	    (Hidden, FunV (Arg Hidden a) _)
		| not $ sameName (nameOf e) (nameInPi $ unEl t0') -> do
		    u  <- newValueMeta a
		    let arg = Arg Hidden u
		    (us, t0'',cs') <- checkArguments r (Arg h e : args)
					   (piApply t0' [arg]) t1
		    return (arg : us, t0'', cs ++ cs')
	    (_, FunV (Arg h' a) _) | h == h' -> do
		u  <- checkExpr e' a
		let arg = Arg h u
		(us, t0'', cs') <- checkArguments (fuseRange r e) args (piApply t0' [arg]) t1
		return (arg : us, t0'', cs ++ cs')
	    (Hidden, FunV (Arg NotHidden _) _) ->
		typeError $ WrongHidingInApplication t0'
	    _ -> __IMPOSSIBLE__
    where
	name (Named _ (A.Var x)) = show x
	name (Named (Just x) _)    = x
	name _			   = "x"

	sameName Nothing _  = True
	sameName n1	 n2 = n1 == n2

	nameInPi (Pi _ b)  = Just $ absName b
	nameInPi (Fun _ _) = Nothing
	nameInPi _	   = __IMPOSSIBLE__


-- | Check that a list of arguments fits a telescope.
checkArguments_ :: Range -> [NamedArg A.Expr] -> Telescope -> TCM (Args, Constraints)
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

bindBuiltinEqual :: A.Expr -> TCM ()
bindBuiltinEqual e = do
    let set = sort (Type 0)
	el  = El (Type 0)
	el1 = El (Type 1)
	vz  = Var 0 []
	nhid = Arg NotHidden
	t   = el1 $ Pi (Arg Hidden set) $ Abs "A"
	    $ el1 $ Fun (nhid $ el vz) $ el1 $ Fun (nhid $ el vz) set
    eq <- checkExpr e t
    bindBuiltinName builtinEquality eq

bindBuiltinRefl :: A.Expr -> TCM ()
bindBuiltinRefl e = do
    eq <- primEqual
    let set = sort (Type 0)
	el  = El (Type 0)
	el1 = El (Type 1)
	vz  = Var 0 []
	hpi x a t = Pi (Arg Hidden a) $ Abs x $ el t
	t   = el1 $ hpi "A" set $ hpi "x" (el vz)
		  $ eq `apply` 
		    (Arg Hidden (Var 1 []) : map (Arg NotHidden) [vz,vz])
    refl <- checkExpr e t
    bindBuiltinName builtinRefl refl

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
	nilType = telePi (telFromList [Arg Hidden ("A",set)]) $ list (Var 0 [])
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
	hPi x a b = telePi (telFromList [Arg Hidden (x,a)]) b
	fun a b	  = el $ Fun (Arg NotHidden a) b
	consType  = hPi "A" set $ el a `fun` (list a `fun` list a)
    cons <- checkExpr e consType
    bindBuiltinName builtinCons cons

bindBuiltinPrimitive :: String -> String -> A.Expr -> (Term -> TCM ()) -> TCM ()
bindBuiltinPrimitive name builtin (A.ScopedExpr scope e) verify = do
  setScope scope
  bindBuiltinPrimitive name builtin e verify
bindBuiltinPrimitive name builtin e@(A.Def qx) verify = do
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
	    addCtxs xs (Arg NotHidden nat) $ f (@@) zero suc (==) choice

-- | Bind a builtin thing to an expression.
bindBuiltin :: String -> A.Expr -> TCM ()
bindBuiltin b e = do
    top <- (== 0) . size <$> getContextTelescope
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
	    | b == builtinEquality		 = bindBuiltinEqual e
	    | b == builtinRefl			 = bindBuiltinRefl e
	    | otherwise				 = typeError $ NoSuchBuiltinName b

---------------------------------------------------------------------------
-- * To be moved somewhere else
---------------------------------------------------------------------------

buildLam :: [Arg String] -> Term -> Term
buildLam xs t = foldr (\ (Arg h x) t -> Lam h (Abs x t)) t xs



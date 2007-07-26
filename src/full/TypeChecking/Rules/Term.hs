{-# OPTIONS -fglasgow-exts -cpp #-}

module TypeChecking.Rules.Term where

import Control.Applicative
import Control.Monad.Trans

import qualified Syntax.Abstract as A
import Syntax.Common
import Syntax.Internal
import Syntax.Position
import Syntax.Literal
import Syntax.Abstract.Views
import qualified Syntax.Info as Info

import TypeChecking.Monad
import TypeChecking.Monad.Builtin
import TypeChecking.Substitute
import TypeChecking.Reduce
import TypeChecking.MetaVars
import TypeChecking.Pretty
import TypeChecking.Records
import TypeChecking.Conversion

import Utils.Monad
import Utils.Size

#include "../../undefined.h"

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
-- * Literal
---------------------------------------------------------------------------

checkLiteral :: Literal -> Type -> TCM Term
checkLiteral lit t = do
    t' <- litType lit
    v  <- blockTerm t (Lit lit) $ equalType t t'
    return v

litType :: Literal -> TCM Type
litType l = case l of
    LitInt _ _	  -> el <$> primNat
    LitFloat _ _  -> el <$> primFloat
    LitChar _ _   -> el <$> primChar
    LitString _ _ -> el <$> primString
  where
    el t = El (Type 0) t

---------------------------------------------------------------------------
-- * Terms
---------------------------------------------------------------------------

-- | Type check an expression.
checkExpr :: A.Expr -> Type -> TCM Term
checkExpr e t =
    traceCall (CheckExpr e t) $ localScope $ do
    reportSDoc "tc.term.expr.top" 15 $
        text "Checking" <+> sep
	  [ fsep [ prettyTCM e, text ":", prettyTCM t ]
	  , nest 2 $ text "at " <+> (text . show =<< getCurrentRange)
	  ]
    t <- reduce t
    reportSDoc "tc.term.expr.top" 15 $
        text "    --> " <+> prettyTCM t
    let scopedExpr (A.ScopedExpr scope e) = setScope scope >> scopedExpr e
	scopedExpr e			  = return e
    e <- scopedExpr e
    case e of

	-- Insert hidden lambda if appropriate
	_   | not (hiddenLambda e)
	    , FunV (Arg Hidden _) _ <- funView (unEl t) -> do
		x <- freshName r (argName t)
                reportSLn "tc.term.expr.impl" 15 $ "Inserting implicit lambda"
		checkExpr (A.Lam (Info.ExprRange $ getRange e) (A.DomainFree Hidden x) e) t
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
		(vs, t1, cs) <- checkArguments ExpandLast (getRange hd) args t0 t
		blockTerm t (f vs) $ (cs ++) <$> equalType t1 t

	A.WithApp _ e es -> typeError $ NotImplemented "type checking of with application"

	A.App i e arg -> do
	    (v0, t0)	 <- inferExpr e
	    (vs, t1, cs) <- checkArguments ExpandLast (getRange e) [arg] t0 t
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
	      (args, cs) <- checkArguments_ ExpandLast (getRange e)
			      (map (Arg NotHidden . unnamed) es) tel
	      blockTerm t (Con r args) $ return cs
            MetaV _ _ -> postponeTypeCheckingProblem e t
	    _         -> typeError $ ShouldBeRecordType t

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

data ExpandHidden = ExpandLast | DontExpandLast

-- | Check a list of arguments: @checkArgs args t0 t1@ checks that
--   @t0 = Delta -> t0'@ and @args : Delta@. Inserts hidden arguments to
--   make this happen. Returns @t0'@ and any constraints that have to be
--   solve for everything to be well-formed.
--   TODO: doesn't do proper blocking of terms
checkArguments :: ExpandHidden -> Range -> [NamedArg A.Expr] -> Type -> Type -> TCM (Args, Type, Constraints)
checkArguments DontExpandLast _ [] t0 t1 = return ([], t0, [])
checkArguments exh r [] t0 t1 =
    traceCall (CheckArguments r [] t0 t1) $ do
	t0' <- reduce t0
	t1' <- reduce t1
	case funView $ unEl t0' of -- TODO: clean
	    FunV (Arg Hidden a) _ | notHPi $ unEl t1'  -> do
		v  <- newValueMeta a
		let arg = Arg Hidden v
		(vs, t0'',cs) <- checkArguments exh r [] (piApply t0' [arg]) t1'
		return (arg : vs, t0'',cs)
	    _ -> return ([], t0', [])
    where
	notHPi (Pi  (Arg Hidden _) _) = False
	notHPi (Fun (Arg Hidden _) _) = False
	notHPi _		      = True

checkArguments exh r args0@(Arg h e : args) t0 t1 =
    traceCall (CheckArguments r args0 t0 t1) $ do
	(t0', cs) <- forcePi h (name e) t0
	e' <- return $ namedThing e
	case (h, funView $ unEl t0') of
	    (NotHidden, FunV (Arg Hidden a) _) -> do
		u  <- newValueMeta a
		let arg = Arg Hidden u
		(us, t0'',cs') <- checkArguments exh r (Arg h e : args)
				       (piApply t0' [arg]) t1
		return (arg : us, t0'', cs ++ cs')
	    (Hidden, FunV (Arg Hidden a) _)
		| not $ sameName (nameOf e) (nameInPi $ unEl t0') -> do
		    u  <- newValueMeta a
		    let arg = Arg Hidden u
		    (us, t0'',cs') <- checkArguments exh r (Arg h e : args)
					   (piApply t0' [arg]) t1
		    return (arg : us, t0'', cs ++ cs')
	    (_, FunV (Arg h' a) _) | h == h' -> do
		u  <- checkExpr e' a
		let arg = Arg h u
		(us, t0'', cs') <- checkArguments exh (fuseRange r e) args (piApply t0' [arg]) t1
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
checkArguments_ :: ExpandHidden -> Range -> [NamedArg A.Expr] -> Telescope -> TCM (Args, Constraints)
checkArguments_ exh r args tel = do
    (args, _, cs) <- checkArguments exh r args (telePi tel $ sort Prop) (sort Prop)
    return (args, cs)


-- | Infer the type of an expression. Implemented by checking agains a meta
--   variable.
inferExpr :: A.Expr -> TCM (Term, Type)
inferExpr e = do
    t <- newTypeMeta_
    v <- checkExpr e t
    return (v,t)

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


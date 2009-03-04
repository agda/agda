{-# LANGUAGE CPP, PatternGuards #-}

module Agda.TypeChecking.Rules.Term where

import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.Error
import Data.Maybe
import Data.List hiding (sort)
import qualified System.IO.UTF8 as UTF8

import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Info as A
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Abstract.Views

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Constraints

import Agda.Utils.Tuple
import Agda.Utils.Permutation

import {-# SOURCE #-} Agda.TypeChecking.Empty (isEmptyTypeC)
import {-# SOURCE #-} Agda.TypeChecking.Rules.Decl (checkSectionApplication)

import Agda.Utils.Monad
import Agda.Utils.Size

#include "../../undefined.h"
import Agda.Utils.Impossible

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
    v  <- blockTerm t (Lit lit) $ leqType t' t
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

-- TODO: move somewhere suitable
reduceCon :: MonadTCM tcm => QName -> tcm QName
reduceCon c = do
  Con c [] <- constructorForm =<< reduce (Con c [])
  return c

checkArguments' exph r args t0 t e k = do
  z <- runErrorT $ checkArguments exph r args t0 t
  case z of
    Right (vs, t1, cs) -> k vs t1 cs
    Left t0 -> do
      let unblock = do
            t0 <- reduceB $ unEl t0
            case t0 of
              Blocked{}          -> return False
              NotBlocked MetaV{} -> return False
              _                  -> return True
      postponeTypeCheckingProblem e t unblock

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
	_   | not (hiddenLambdaOrHole e)
	    , FunV (Arg Hidden _) _ <- funView (unEl t) -> do
		x <- freshName r (argName t)
                reportSLn "tc.term.expr.impl" 15 $ "Inserting implicit lambda"
		checkExpr (A.Lam (A.ExprRange $ getRange e) (A.DomainFree Hidden x) e) t
	    where
		r = case rStart $ getRange e of
                      Nothing  -> noRange
                      Just pos -> posToRange pos pos

                hiddenLambdaOrHole (A.AbsurdLam _ Hidden)                                  = True
		hiddenLambdaOrHole (A.Lam _ (A.DomainFree Hidden _) _)			   = True
		hiddenLambdaOrHole (A.Lam _ (A.DomainFull (A.TypedBindings _ Hidden _)) _) = True
		hiddenLambdaOrHole (A.QuestionMark _)					   = True
		hiddenLambdaOrHole _							   = False

	-- Variable or constant application
	_   | Application (HeadCon cs@(_:_:_)) args <- appView e -> do
                -- First we should figure out which constructor we want.
                reportSLn "tc.check.term" 40 $ "Ambiguous constructor: " ++ show cs

                -- Get the datatypes of the various constructors
                let getData Constructor{conData = d} = d
                    getData _                        = __IMPOSSIBLE__
                reportSLn "tc.check.term" 40 $ "  ranges before: " ++ show (getRange cs)
                cs  <- zipWith setRange (map getRange cs) <$> mapM reduceCon cs
                reportSLn "tc.check.term" 40 $ "  ranges after: " ++ show (getRange cs)
                reportSLn "tc.check.term" 40 $ "  reduced: " ++ show cs
                dcs <- mapM (\c -> (getData /\ const c) . theDef <$> getConstInfo c) cs

                -- Lets look at the target type at this point
                let getCon = do
                      t <- normalise t
                      let TelV _ t1 = telView t
                      t1 <- reduceB $ unEl t1
                      case t1 of
                        NotBlocked (Def d _) -> do
                          defn <- theDef <$> getConstInfo d
                          case defn of
                            Datatype{} ->
                              case [ c | (d', c) <- dcs, d == d' ] of
                                c:_   -> return (Just c)
                                []    -> fail $ show (head cs) ++ " does not construct an element of the datatype " ++ show d
                            _ -> return Nothing
                        NotBlocked (MetaV _ _)  -> return Nothing
                        Blocked{} -> return Nothing
                             -- TODO: error message
                        _ -> fail $ show (head cs) ++ " does not construct an element of " ++ show t
                let unblock = isJust <$> getCon
                mc <- getCon
                case mc of
                  Just c -> do
                    let hd = HeadCon [c]
                    (f,  t0)     <- inferHead hd
                    checkArguments' ExpandLast (getRange hd) args t0 t e $ \vs t1 cs ->
                      blockTerm t (f vs) $ (cs ++) <$> leqType t1 t
                  Nothing -> postponeTypeCheckingProblem e t unblock

            | Application hd args <- appView e -> do
		(f,  t0)     <- inferHead hd
                checkArguments' ExpandLast (getRange hd) args t0 t e $ \vs t1 cs ->
                    blockTerm t (f vs) $ (cs ++) <$> leqType t1 t

	A.WithApp _ e es -> typeError $ NotImplemented "type checking of with application"

	A.App i e arg -> do
	    (v0, t0)	 <- inferExpr e
	    checkArguments' ExpandLast (getRange e) [arg] t0 t e $ \vs t1 cs ->
	      blockTerm t (apply v0 vs) $ (cs ++) <$> leqType t1 t

        A.AbsurdLam i h -> do
          t <- reduceB t
          case t of
            Blocked{}                 -> postponeTypeCheckingProblem_ e $ ignoreBlocking t
            NotBlocked (El _ MetaV{}) -> postponeTypeCheckingProblem_ e $ ignoreBlocking t
            NotBlocked t' -> case funView $ unEl t' of
              FunV (Arg h' a) _
                | h == h' -> do
                  cs' <- isEmptyTypeC a
                  -- Add helper function
                  top <- currentModule
                  let name = "absurd"
                  aux <- qualify top <$> freshName (getRange i) name
                  reportSDoc "tc.term.absurd" 10 $ vcat
                    [ text "Adding absurd function" <+> prettyTCM aux
                    , nest 2 $ text "of type" <+> prettyTCM t'
                    ]
                  addConstant aux $ Defn aux t' (defaultDisplayForm aux) 0
                                  $ Function
                                    { funClauses        =
                                        [Clause { clauseRange = getRange e
                                                , clauseTel   = EmptyTel
                                                , clausePerm  = Perm 0 []
                                                , clausePats  = [Arg h $ VarP "()"]
                                                , clauseBody  = NoBody
                                                }
                                        ]
                                    , funInv            = NotInjective
                                    , funAbstr          = ConcreteDef
                                    , funPolarity       = [Covariant]
                                    , funArgOccurrences = [Unused]
                                    }
                  blockTerm t' (Def aux []) $ return cs'
                | otherwise -> typeError $ WrongHidingInLambda t'
              _ -> typeError $ ShouldBePi t'

	A.Lam i (A.DomainFull b) e -> do
	    (v, cs) <- checkTypedBindings b $ \tel -> do
	        t1 <- newTypeMeta_
                cs <- escapeContext (size tel) $ leqType (telePi tel t1) t
                v <- checkExpr e t1
                return (teleLam tel v, cs)
	    blockTerm t v (return cs)
	    where
		name (Arg h (x,_)) = Arg h x

	A.Lam i (A.DomainFree h x) e0 -> do
	    -- (t',cs) <- forcePi h (show x) t
            t <- reduceB t
            case t of
              Blocked{}                 -> postponeTypeCheckingProblem_ e $ ignoreBlocking t
              NotBlocked (El _ MetaV{}) -> postponeTypeCheckingProblem_ e $ ignoreBlocking t
              NotBlocked t' -> case funView $ unEl t' of
		FunV arg0@(Arg h' a) _
		    | h == h' -> do
			v <- addCtx x arg0 $ do
                              let arg = Arg h (Var 0 [])
                                  tb  = raise 1 t' `piApply` [arg]
                              v <- checkExpr e0 tb
                              return $ Lam h $ Abs (show x) v
			-- blockTerm t v (return cs)
                        return v
		    | otherwise ->
			typeError $ WrongHidingInLambda t'
		_   -> typeError $ ShouldBePi t'

	A.QuestionMark i -> do
	    setScope (A.metaScope i)
	    newQuestionMark  t
	A.Underscore i   -> do
	    setScope (A.metaScope i)
	    newValueMeta t

	A.Lit lit    -> checkLiteral lit t
	A.Let i ds e -> checkLetBindings ds $ checkExpr e t
	A.Pi _ tel e -> do
	    t' <- checkTelescope tel $ \tel -> telePi_ tel <$> isType_ e
	    blockTerm t (unEl t') $ leqType (sort $ getSort t') t
	A.Fun _ (Arg h a) b -> do
	    a' <- isType_ a
	    b' <- isType_ b
	    let s = getSort a' `sLub` getSort b'
	    blockTerm t (Fun (Arg h a') b') $ leqType (sort s) t
	A.Set _ n    -> do
          n <- ifM typeInType (return 0) (return n)
	  blockTerm t (Sort (Type n)) $ leqType (sort $ Type $ n + 1) t
	A.Prop _     -> do
          s <- ifM typeInType (return $ Type 0) (return Prop)
	  blockTerm t (Sort Prop) $ leqType (sort $ Type 1) t

	A.Rec _ fs  -> do
	  t <- normalise t
	  case unEl t of
	    Def r vs  -> do
	      xs    <- getRecordFieldNames r
	      ftel  <- getRecordFieldTypes r
              scope <- getScope
              let meta = A.Underscore $ A.MetaInfo (getRange e) scope Nothing
	      es   <- orderFields r meta xs fs
	      let tel = ftel `apply` vs
	      (args, cs) <- checkArguments_ ExpandLast (getRange e)
			      (map (Arg NotHidden . unnamed) es) tel
	      blockTerm t (Con (killRange r) args) $ return cs
            MetaV _ _ -> do
              reportSDoc "tc.term.expr.rec" 10 $ sep
                [ text "Postponing type checking of"
                , nest 2 $ prettyA e <+> text ":" <+> prettyTCM t
                ]
              postponeTypeCheckingProblem_ e t
	    _         -> typeError $ ShouldBeRecordType t

	A.Var _    -> __IMPOSSIBLE__
	A.Def _    -> __IMPOSSIBLE__
	A.Con _    -> __IMPOSSIBLE__

	A.ScopedExpr scope e -> setScope scope >> checkExpr e t

-- | Infer the type of a head thing (variable, function symbol, or constructor)
inferHead :: Head -> TCM (Args -> Term, Type)
inferHead (HeadVar x) = do -- traceCall (InferVar x) $ do
  (u, a) <- getVarInfo x
  return (apply u, a)
inferHead (HeadDef x) = do
  (u, a) <- inferDef Def x
  return (apply u, a)
inferHead (HeadCon [c]) = do

  -- Constructors are polymorphic internally so when building the constructor
  -- term we should throw away arguments corresponding to parameters.

  -- First, inferDef will try to apply the constructor to the free parameters
  -- of the current context. We ignore that.
  (u, a) <- inferDef (\c _ -> Con c []) c

  -- Next get the number of parameters in the current context.
  Constructor{conPars = n} <- theDef <$> (instantiateDef =<< getConstInfo c)

  verboseS "tc.term.con" 7 $ do
    liftIO $ UTF8.putStrLn $ unwords [show c, "has", show n, "parameters."]

  -- So when applying the constructor throw away the parameters.
  return (apply u . genericDrop n, a)
inferHead (HeadCon _) = __IMPOSSIBLE__  -- inferHead will only be called on unambiguous constructors

inferDef :: (QName -> Args -> Term) -> QName -> TCM (Term, Type)
inferDef mkTerm x =
    traceCall (InferDef (getRange x) x) $ do
    d  <- instantiateDef =<< getConstInfo x
    vs <- freeVarsToApply x
    verboseS "tc.term.def" 10 $ do
      ds <- mapM prettyTCM vs
      dx <- prettyTCM x
      dt <- prettyTCM $ defType d
      liftIO $ UTF8.putStrLn $ "inferred def " ++ unwords (show dx : map show ds) ++ " : " ++ show dt
    return (mkTerm x vs, defType d)

data ExpandHidden = ExpandLast | DontExpandLast

instance Error Type where
  strMsg _ = __IMPOSSIBLE__
  noMsg = __IMPOSSIBLE__

traceCallE :: Error e => (Maybe r -> Call) -> ErrorT e TCM r -> ErrorT e TCM r
traceCallE call m = do
  z <- lift $ traceCall call' $ runErrorT m
  case z of
    Right e  -> return e
    Left err -> throwError err
  where
    call' Nothing          = call Nothing
    call' (Just (Left _))  = call Nothing
    call' (Just (Right x)) = call (Just x)

-- | Check a list of arguments: @checkArgs args t0 t1@ checks that
--   @t0 = Delta -> t0'@ and @args : Delta@. Inserts hidden arguments to
--   make this happen. Returns @t0'@ and any constraints that have to be
--   solve for everything to be well-formed.
--   TODO: doesn't do proper blocking of terms
checkArguments :: ExpandHidden -> Range -> [NamedArg A.Expr] -> Type -> Type -> ErrorT Type TCM (Args, Type, Constraints)
checkArguments DontExpandLast _ [] t0 t1 = return ([], t0, [])
checkArguments exh r [] t0 t1 =
    traceCallE (CheckArguments r [] t0 t1) $ do
	t0' <- lift $ reduce t0
	t1' <- lift $ reduce t1
	case funView $ unEl t0' of -- TODO: clean
	    FunV (Arg Hidden a) _ | notHPi $ unEl t1'  -> do
		v  <- lift $ newValueMeta a
		let arg = Arg Hidden v
		(vs, t0'',cs) <- checkArguments exh r [] (piApply t0' [arg]) t1'
		return (arg : vs, t0'',cs)
	    _ -> return ([], t0', [])
    where
	notHPi (Pi  (Arg Hidden _) _) = False
	notHPi (Fun (Arg Hidden _) _) = False
	notHPi _		      = True

checkArguments exh r args0@(Arg h e : args) t0 t1 =
    traceCallE (CheckArguments r args0 t0 t1) $ do
      t0b <- lift $ reduceB t0
      case t0b of
        Blocked{}                 -> throwError $ ignoreBlocking t0b
        NotBlocked (El _ MetaV{}) -> throwError $ ignoreBlocking t0b
        NotBlocked t0' -> do
          -- (t0', cs) <- forcePi h (name e) t0
          e' <- return $ namedThing e
          case (h, funView $ unEl t0') of
              (NotHidden, FunV (Arg Hidden a) _) -> insertUnderscore
              (Hidden, FunV (Arg Hidden a) _)
                  | not $ sameName (nameOf e) (nameInPi $ unEl t0') -> insertUnderscore
              (_, FunV (Arg h' a) _) | h == h' -> do
                  u  <- lift $ checkExpr e' a
                  let arg = Arg h u
                  (us, t0'', cs') <- checkArguments exh (fuseRange r e) args (piApply t0' [arg]) t1
                  return (arg : us, t0'', cs')
              (Hidden, FunV (Arg NotHidden _) _) ->
                  lift $ typeError $ WrongHidingInApplication t0'
              _ -> lift $ typeError $ ShouldBePi t0'
    where
	insertUnderscore = do
	  scope <- lift $ getScope
	  let m = A.Underscore $ A.MetaInfo
		  { A.metaRange  = r
		  , A.metaScope  = scope
		  , A.metaNumber = Nothing
		  }
	  checkArguments exh r (Arg Hidden (unnamed m) : args0) t0 t1

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
    z <- runErrorT $ checkArguments exh r args (telePi tel $ sort Prop) (sort Prop)
    case z of
      Right (args, _, cs) -> return (args, cs)
      Left _              -> __IMPOSSIBLE__


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
checkLetBinding (A.LetApply i x tel m args rd rm) ret = do
  -- Any variables in the context that doesn't belong to the current
  -- module should go with the new module.
  fv   <- getDefFreeVars =<< (qnameFromList . mnameToList) <$> currentModule
  n    <- size <$> getContext
  let new = n - fv
  reportSLn "tc.term.let.apply" 10 $ "Applying " ++ show m ++ " with " ++ show new ++ " free variables"
  checkSectionApplication i x tel m args rd rm
  withAnonymousModule x new ret


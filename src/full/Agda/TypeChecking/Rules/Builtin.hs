{-# OPTIONS -fglasgow-exts #-}

module Agda.TypeChecking.Rules.Builtin where

import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Data.Maybe

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import Agda.Syntax.Common

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Constraints

import Agda.TypeChecking.Rules.Term ( checkExpr )

import Agda.Utils.Size

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

typeOfSizeInf :: TCM Type
typeOfSizeInf = do
    sz  <- primSize
    return $ (El (Type 0) sz)

typeOfSizeSuc :: TCM Type
typeOfSizeSuc = do
    sz  <- primSize
    let	sz' = El (Type 0) sz
    return $ El (Type 0) $ Fun (Arg NotHidden sz') sz'

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
	a   = defAbstract info
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
    , "NATEQUALS" |-> ("primNatEquality", verifyEquals)
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
		zero  - zero  == zero
		zero  - suc m == zero
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

-- | Builtin constructors
builtinConstructors :: [(String, A.Expr -> TCM ())]
builtinConstructors =
  [ (builtinNil,     bindBuiltinNil               )
  , (builtinCons,    bindBuiltinCons              )
  , (builtinZero,    bindBuiltinZero              )
  , (builtinSuc,     bindBuiltinSuc               )
  , (builtinTrue,    bindBuiltinBool builtinTrue  )
  , (builtinFalse,   bindBuiltinBool builtinFalse )
  ]

-- | Builtin postulates
builtinPostulates :: [(String, TCM Type)]
builtinPostulates =
  [ (builtinSize,    return $ sort $ Type 0 )
  , (builtinSizeSuc, typeOfSizeSuc          )
  , (builtinSizeInf, typeOfSizeInf          )
  ]

-- | Bind a builtin constructor. Pre-condition: argument is an element of
--   'builtinConstructors'.
bindConstructor :: String -> (A.Expr -> TCM ()) -> A.Expr -> TCM ()
bindConstructor s bind (A.ScopedExpr scope e) = do
  setScope scope
  bindConstructor s bind e
bindConstructor s bind e@(A.Con _) = bind e
bindConstructor s _ e              = typeError $ BuiltinMustBeConstructor s e

-- | Bind a builtin postulate. Pre-condition: argument is an element of
--   'builtinPostulates'.
bindPostulate :: String -> TCM Type -> A.Expr -> TCM ()
bindPostulate s typ e = do
  t <- typ
  v <- checkExpr e t

  let bad = typeError $ GenericError $ "The builtin " ++ s ++ " must be bound to a postulated identifier."

  case v of
    Def c []  -> ignoreAbstractMode $ do
      defn <- theDef <$> getConstInfo c
      case defn of
        Axiom{} -> return ()
        _       -> bad
    _         -> bad

  bindBuiltinName s v

-- | Bind a builtin thing to an expression.
bindBuiltin :: String -> A.Expr -> TCM ()
bindBuiltin b e = do
    top <- (== 0) . size <$> getContextTelescope
    unless top $ typeError $ BuiltinInParameterisedModule b
    bind b e
    where
	bind b e
	    | elem b builtinTypes                        = bindBuiltinType b e
	    | elem b [builtinList]                       = bindBuiltinType1 b e
            | Just bind  <- lookup b builtinConstructors = bindConstructor b bind e
	    | Just (s,v) <- lookup b builtinPrimitives   = bindBuiltinPrimitive s b e v
            | Just typ   <- lookup b builtinPostulates   = bindPostulate b typ e
	    | otherwise                                  = typeError $ NoSuchBuiltinName b


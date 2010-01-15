{-# LANGUAGE PatternGuards, CPP #-}
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
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty

import Agda.TypeChecking.Rules.Term ( checkExpr )

import Agda.Utils.Size
import Agda.Utils.Impossible

#include "../..//undefined.h"

---------------------------------------------------------------------------
-- * Checking builtin pragmas
---------------------------------------------------------------------------

-- Buitin datatypes and the number of constructors
builtinDatatypes :: [(String, Int)]
builtinDatatypes =
  [ (builtinList, 2)
  , (builtinBool, 2)
  , (builtinNat, 2)
  , (builtinLevel, 2)
  ]

inductiveCheck :: String -> Term -> TCM ()
inductiveCheck b t =
  case lookup b builtinDatatypes of
    Nothing -> return ()
    Just n  -> do
      t <- normalise t
      let err = typeError (NotInductive t)
      case t of
        Def t _ -> do
          t <- theDef <$> getConstInfo t
          case t of
            Datatype { dataInduction = Inductive
                     , dataCons      = cs
                     }
              | length cs == n -> return ()
              | otherwise ->
                typeError $ GenericError $ unwords
                            [ "The builtin", b
                            , "must be a datatype with", show n
                            , "constructors" ]
            _ -> err
        _ -> err

bindBuiltinType :: String -> A.Expr -> TCM ()
bindBuiltinType b e = do
    let s = sort $ mkType 0
    reportSDoc "tc.builtin" 20 $ text "checking builtin type" <+> prettyA e <+> text ":" <+> text (show s)
    t <- checkExpr e (sort $ mkType 0)
    inductiveCheck b t
    bindBuiltinName b t

    -- NAT and LEVEL must be different. (Why?)
    when (b `elem` [builtinNat, builtinLevel]) $ do
      nat   <- getBuiltin' builtinNat
      level <- getBuiltin' builtinLevel
      case (nat, level) of
        (Just nat, Just level) -> do
          Def nat   _ <- normalise nat
          Def level _ <- normalise level
          when (nat == level) $ typeError $ GenericError $
            builtinNat ++ " and " ++ builtinLevel ++
            " have to be different types."
        _ -> return ()

bindBuiltinBool :: String -> A.Expr -> TCM Term
bindBuiltinBool b e = do
    bool <- primBool
    checkExpr e $ El (mkType 0) bool

-- | Bind something of type @Set -> Set@.
bindBuiltinType1 :: String -> A.Expr -> TCM ()
bindBuiltinType1 thing e = do
    let set      = sort (mkType 0)
        setToSet = El (mkType 1) $ Fun (Arg NotHidden set) set
    f <- checkExpr e setToSet
    inductiveCheck thing f
    bindBuiltinName thing f

bindBuiltinZero' :: String -> TCM Term -> A.Expr -> TCM Term
bindBuiltinZero' bZero pNat e = do
    nat  <- pNat
    checkExpr e (El (mkType 0) nat)

bindBuiltinSuc' :: String -> TCM Term -> A.Expr -> TCM Term
bindBuiltinSuc' bSuc pNat e = do
    nat  <- pNat
    let nat' = El (mkType 0) nat
        natToNat = El (mkType 0) $ Fun (Arg NotHidden nat') nat'
    checkExpr e natToNat

bindBuiltinZero e = bindBuiltinZero' builtinZero primNat e
bindBuiltinSuc  e = bindBuiltinSuc'  builtinSuc primNat e

bindBuiltinLevelZero e = bindBuiltinZero' builtinLevelZero primLevel e
bindBuiltinLevelSuc  e = bindBuiltinSuc'  builtinLevelSuc  primLevel e

typeOfSizeInf :: TCM Type
typeOfSizeInf = do
    sz  <- primSize
    return $ (El (mkType 0) sz)

typeOfSizeSuc :: TCM Type
typeOfSizeSuc = do
    sz  <- primSize
    let sz' = El (mkType 0) sz
    return $ El (mkType 0) $ Fun (Arg NotHidden sz') sz'

-- | Built-in nil should have type @{A:Set} -> List A@
bindBuiltinNil :: A.Expr -> TCM Term
bindBuiltinNil e = do
    list' <- primList
    let set     = sort (mkType 0)
        list a  = El (mkType 0) (list' `apply` [Arg NotHidden a])
        nilType = telePi (telFromList [Arg Hidden ("A",set)]) $ list (Var 0 [])
    checkExpr e nilType

-- | Built-in cons should have type @{A:Set} -> A -> List A -> List A@
bindBuiltinCons :: A.Expr -> TCM Term
bindBuiltinCons e = do
    list' <- primList
    let set       = sort (mkType 0)
        el        = El (mkType 0)
        a         = Var 0 []
        list x    = el $ list' `apply` [Arg NotHidden x]
        hPi x a b = telePi (telFromList [Arg Hidden (x,a)]) b
        fun a b   = el $ Fun (Arg NotHidden a) b
        consType  = hPi "A" set $ el a `fun` (list a `fun` list a)
    checkExpr e consType

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
    addConstant qx $ info { theDef = Primitive a name (Just cls) }

    -- needed? yes, for checking equations for mul
    bindBuiltinName builtin v
bindBuiltinPrimitive _ b _ _ = typeError $ GenericError $ "Builtin " ++ b ++ " must be bound to a function"

builtinPrimitives :: [ (String, (String, Term -> TCM ())) ]
builtinPrimitives =
    [ "NATPLUS"       |-> ("primNatPlus", verifyPlus)
    , "NATMINUS"      |-> ("primNatMinus", verifyMinus)
    , "NATTIMES"      |-> ("primNatTimes", verifyTimes)
    , "NATDIVSUCAUX"  |-> ("primNatDivSucAux", verifyDivSucAux)
    , "NATMODSUCAUX"  |-> ("primNatModSucAux", verifyModSucAux)
    , "NATEQUALS"     |-> ("primNatEquality", verifyEquals)
    , "NATLESS"       |-> ("primNatLess", verifyLess)
    , builtinLevelMax |-> ("primLevelMax", verifyMax)
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

        verifyDivSucAux dsAux =
            verify ["k","m","n","j"] $ \(@@) zero suc (==) choice -> do
                let aux k m n j = dsAux @@ k @@ m @@ n @@ j
                    k           = Var 0 []
                    m           = Var 1 []
                    n           = Var 2 []
                    j           = Var 3 []

                aux k m zero    j       == k
                aux k m (suc n) zero    == aux (suc k) m n m
                aux k m (suc n) (suc j) == aux k m n j

        verifyModSucAux dsAux =
            verify ["k","m","n","j"] $ \(@@) zero suc (==) choice -> do
                let aux k m n j = dsAux @@ k @@ m @@ n @@ j
                    k           = Var 0 []
                    m           = Var 1 []
                    n           = Var 2 []
                    j           = Var 3 []

                aux k m zero    j       == k
                aux k m (suc n) zero    == aux zero m n m
                aux k m (suc n) (suc j) == aux (suc k) m n j

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

        verifyMax maxV =
            verify' primLevel primLevelZero primLevelSuc ["n","m"] $
              \(@@) zero suc (==) choice -> do
                let m = Var 0 []
                    n = Var 1 []
                    max x y = maxV @@ x @@ y

                max zero (suc n)    == suc n
                max (suc n) zero    == suc n
                max (suc n) (suc m) == suc (max n m)

        verify xs = verify' primNat primZero primSuc xs

        verify' ::  TCM Term -> TCM Term -> TCM Term ->
                    [String] -> ( (Term -> Term -> Term) -> Term -> (Term -> Term) ->
                                (Term -> Term -> TCM ()) ->
                                ([TCM ()] -> TCM ()) -> TCM a) -> TCM a
        verify' pNat pZero pSuc xs f = do
            nat  <- El (mkType 0) <$> pNat
            zero <- pZero
            s    <- pSuc
            let x @@ y = x `apply` [Arg NotHidden y]
                x == y = noConstraints $ equalTerm nat x y
                suc n  = s @@ n
                choice = foldr1 (\x y -> x `catchError` \_ -> y)
            xs <- mapM freshName_ xs
            addCtxs xs (Arg NotHidden nat) $ f (@@) zero suc (==) choice

bindBuiltinEquality :: A.Expr -> TCM ()
bindBuiltinEquality e = do
  let set       = sort (mkType 0)
      el        = El (mkType 0)
      a         = Var 0 []
      hPi x a b = telePi (telFromList [Arg Hidden (x,a)]) b
      fun a b   = El (mkType 1) $ Fun (Arg NotHidden a) b
      eqType    = hPi "A" set $ el a `fun` (el a `fun` set)
  eq <- checkExpr e eqType
  bindBuiltinName builtinEquality eq


bindBuiltinRefl :: A.Expr -> TCM Term
bindBuiltinRefl e = do
  eq' <- primEquality
  let set       = sort (mkType 0)
      el        = El (mkType 0)
      v0        = Var 0 []
      v1        = Var 1 []
      hPi x a b = telePi (telFromList [Arg Hidden (x, a)]) b
      fun a b   = el $ Fun (Arg NotHidden a) b
      eq a b c  = el $ eq' `apply` [Arg Hidden a, Arg NotHidden b, Arg NotHidden c]
      reflType  = hPi "A" set $ hPi "x" (el v0) $ eq v1 v0 v0
  checkExpr e reflType

-- | Builtin constructors
builtinConstructors :: [(String, A.Expr -> TCM Term)]
builtinConstructors =
  [ (builtinNil,       bindBuiltinNil               )
  , (builtinCons,      bindBuiltinCons              )
  , (builtinZero,      bindBuiltinZero              )
  , (builtinSuc,       bindBuiltinSuc               )
  , (builtinTrue,      bindBuiltinBool builtinTrue  )
  , (builtinFalse,     bindBuiltinBool builtinFalse )
  , (builtinRefl,      bindBuiltinRefl              )
  , (builtinLevelZero, bindBuiltinLevelZero         )
  , (builtinLevelSuc,  bindBuiltinLevelSuc          )
  ]

-- | Builtin postulates
builtinPostulates :: [(String, TCM Type)]
builtinPostulates =
  [ (builtinSize,    return $ sort $ mkType 0 )
  , (builtinSizeSuc, typeOfSizeSuc            )
  , (builtinSizeInf, typeOfSizeInf            )
  ]

-- | Bind a builtin constructor. Pre-condition: argument is an element of
--   'builtinConstructors'.
bindConstructor :: String -> (A.Expr -> TCM Term) -> A.Expr -> TCM ()
bindConstructor s check (A.ScopedExpr scope e) = do
  setScope scope
  bindConstructor s check e
bindConstructor s check e@(A.Con _) = do
  t <- check e
  -- The constructor might have been eta expanded during type checking
  let name (Lam h b) = name (absBody b)
      name (Con c _) = Con c []
      name _         = __IMPOSSIBLE__
  bindBuiltinName s (name t)
bindConstructor s _ e               = typeError $ BuiltinMustBeConstructor s e

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
            | b == builtinEquality                       = bindBuiltinEquality e
            | Just bind  <- lookup b builtinConstructors = bindConstructor b bind e
            | Just (s,v) <- lookup b builtinPrimitives   = bindBuiltinPrimitive s b e v
            | Just typ   <- lookup b builtinPostulates   = bindPostulate b typ e
            | otherwise                                  = typeError $ NoSuchBuiltinName b


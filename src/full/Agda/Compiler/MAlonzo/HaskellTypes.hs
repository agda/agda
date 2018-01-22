{-# LANGUAGE CPP #-}

-- | Translating Agda types to Haskell types. Used to ensure that imported
--   Haskell functions have the right type.

module Agda.Compiler.MAlonzo.HaskellTypes where

import Control.Monad (zipWithM)
import Data.Maybe (fromMaybe)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive (getBuiltinName)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free
import Agda.TypeChecking.Telescope

import Agda.Compiler.MAlonzo.Pragmas
import Agda.Compiler.MAlonzo.Misc
import Agda.Compiler.MAlonzo.Pretty

import qualified Agda.Utils.Haskell.Syntax as HS
import Agda.Utils.Except ( MonadError(catchError) )
import Agda.Utils.Pretty (prettyShow)

#include "undefined.h"
import Agda.Utils.Impossible

type HaskellKind = String

hsStar :: HaskellKind
hsStar = "*"

hsKFun :: HaskellKind -> HaskellKind -> HaskellKind
hsKFun k l = "(" ++ k ++ " -> " ++ l ++ ")"

hsFun :: HaskellKind -> HaskellKind -> HaskellKind
hsFun a b = "(" ++ a ++ " -> " ++ b ++ ")"

hsUnit :: HaskellType
hsUnit = "()"

hsVar :: Name -> HaskellType
hsVar x = "x" ++ concatMap encode (prettyShow x)
  where
    okChars = ['a'..'z'] ++ ['A'..'Y'] ++ "_'"
    encode 'Z' = "ZZ"
    encode c
      | c `elem` okChars = [c]
      | otherwise        = "Z" ++ show (fromEnum c)


hsApp :: String -> [HaskellType] -> HaskellType
hsApp d [] = d
hsApp d as = "(" ++ unwords (d : as) ++ ")"

hsForall :: String -> HaskellType -> HaskellType
hsForall x a = "(forall " ++ x ++ ". " ++ a ++ ")"

notAHaskellType :: Type -> TCM a
notAHaskellType a = typeError . GenericDocError =<< do
  fsep $ pwords "The type" ++ [prettyTCM a] ++
         pwords "cannot be translated to a Haskell type."


getHsType :: QName -> TCM HaskellType
getHsType x = do
  d <- getHaskellPragma x
  list <- getBuiltinName builtinList
  inf  <- getBuiltinName builtinInf
  let namedType = do
        -- For these builtin types, the type name (xhqn ...) refers to the
        -- generated, but unused, datatype and not the primitive type.
        nat  <- getBuiltinName builtinNat
        int  <- getBuiltinName builtinInteger
        bool <- getBuiltinName builtinBool
        if  | Just x `elem` [nat, int] -> return "Integer"
            | Just x == bool           -> return "Bool"
            | otherwise                -> prettyShow <$> xhqn "T" x
  setCurrentRange d $ case d of
    _ | Just x == list -> prettyShow <$> xhqn "T" x -- we ignore Haskell pragmas for List
    _ | Just x == inf  -> return "MAlonzo.RTE.Infinity"
    Just HsDefn{}      -> return hsUnit
    Just HsType{}      -> namedType
    Just HsData{}      -> namedType
    _                  -> notAHaskellType (El Prop $ Def x [])

getHsVar :: Nat -> TCM HaskellCode
getHsVar i = hsVar <$> nameOfBV i

haskellType' :: Type -> TCM HaskellType
haskellType' t = fromType t
  where
    err      = notAHaskellType t
    fromArgs = mapM (fromTerm . unArg)
    fromType = fromTerm . unEl
    fromTerm v = do
      v   <- unSpine <$> reduce v
      reportSLn "compile.haskell.type" 50 $ "toHaskellType " ++ show v
      kit <- liftTCM coinductionKit
      case v of
        Var x es -> do
          let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
          hsApp <$> getHsVar x <*> fromArgs args
        Def d es -> do
          let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
          hsApp <$> getHsType d <*> fromArgs args
        Pi a b ->
          if isBinderUsed b  -- Andreas, 2012-04-03.  Q: could we rely on Abs/NoAbs instead of again checking freeness of variable?
          then do
            hsA <- fromType (unDom a)
            underAbstraction a b $ \b ->
              hsForall <$> getHsVar 0 <*> (hsFun hsA <$> fromType b)
          else hsFun <$> fromType (unDom a) <*> fromType (noabsApp __IMPOSSIBLE__ b)
        Con c ci args -> hsApp <$> getHsType (conName c) <*> fromArgs args
        Lam{}      -> err
        Level{}    -> return hsUnit
        Lit{}      -> return hsUnit
        Sort{}     -> return hsUnit
        Shared p   -> fromTerm $ derefPtr p
        MetaV{}    -> err
        DontCare{} -> err

haskellType :: QName -> TCM HaskellType
haskellType q = do
  def <- getConstInfo q
  let np = case theDef def of
             Constructor{ conPars = np } -> np
             _                           -> 0
      underPars 0 a = haskellType' a
      underPars n a = do
        a <- reduce a
        case unEl a of
          Pi a (NoAbs _ b) -> underPars (n - 1) b
          Pi a b  -> underAbstraction a b $ \b -> hsForall <$> getHsVar 0 <*> underPars (n - 1) b
          _       -> __IMPOSSIBLE__
  ty <- underPars np $ defType def
  reportSLn "tc.pragma.compile" 10 $ "Haskell type for " ++ prettyShow q ++ ": " ++ ty
  return ty

checkConstructorCount :: QName -> [QName] -> [HaskellCode] -> TCM ()
checkConstructorCount d cs hsCons
  | n == hn   = return ()
  | otherwise = do
    let n_forms_are = case hn of
          1 -> "1 Haskell constructor is"
          n -> show n ++ " Haskell constructors are"
        only | hn == 0   = ""
             | hn < n    = "only "
             | otherwise = ""

    genericDocError =<<
      fsep ([prettyTCM d] ++ pwords ("has " ++ show n ++
            " constructors, but " ++ only ++ n_forms_are ++ " given [" ++ unwords hsCons ++ "]"))
  where
    n  = length cs
    hn = length hsCons

-- Type approximations ----------------------------------------------------

data PolyApprox = PolyApprox | NoPolyApprox
  deriving (Eq)

hsTypeApproximation :: PolyApprox -> Int -> Type -> TCM HS.Type
hsTypeApproximation poly fv t = do
  list <- getBuiltinName builtinList
  bool <- getBuiltinName builtinBool
  int  <- getBuiltinName builtinInteger
  nat  <- getBuiltinName builtinNat
  word <- getBuiltinName builtinWord64
  let is q b = Just q == b
      tyCon  = HS.TyCon . HS.UnQual . HS.Ident
      rteCon = HS.TyCon . HS.Qual mazRTE . HS.Ident
      tyVar n i = HS.TyVar $ HS.Ident $ "a" ++ show (n - i)
  let go n t = do
        t <- unSpine <$> reduce t
        case t of
          Var i _ | poly == PolyApprox -> return $ tyVar n i
          Pi a b -> HS.TyFun <$> go n (unEl $ unDom a) <*> go (n + k) (unEl $ unAbs b)
            where k = case b of Abs{} -> 1; NoAbs{} -> 0
          Def q els
            | q `is` list, Apply t <- last ([Proj ProjSystem __IMPOSSIBLE__] ++ els)
                        -> HS.TyApp (tyCon "[]") <$> go n (unArg t)
            | q `is` bool -> return $ tyCon "Bool"
            | q `is` int  -> return $ tyCon "Integer"
            | q `is` nat  -> return $ tyCon "Integer"
            | q `is` word -> return $ rteCon "Word64"
            | otherwise -> do
                let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims els
                foldl HS.TyApp <$> (HS.FakeType <$> getHsType q) <*> mapM (go n . unArg) args
              `catchError` \ _ -> do -- Not a Haskell type
                def <- theDef <$> getConstInfo q
                let isData | Datatype{} <- def = True
                           | Record{}   <- def = True
                           | otherwise         = False
                if isData then HS.TyCon <$> xhqn "T" q
                          else return mazAnyType
          Sort{} -> return $ HS.FakeType "()"
          _ -> return mazAnyType
  go fv (unEl t)

-- Approximating polymorphic types is not actually a good idea unless we
-- actually keep track of type applications in recursive functions, and
-- generate parameterised datatypes. Otherwise we'll just coerce all type
-- variables to `Any` at the first `unsafeCoerce`.
hsTelApproximation :: Type -> TCM ([HS.Type], HS.Type)
hsTelApproximation = hsTelApproximation' NoPolyApprox

hsTelApproximation' :: PolyApprox -> Type -> TCM ([HS.Type], HS.Type)
hsTelApproximation' poly t = do
  TelV tel res <- telView t
  let args = map (snd . unDom) (telToList tel)
  (,) <$> zipWithM (hsTypeApproximation poly) [0..] args <*> hsTypeApproximation poly (length args) res

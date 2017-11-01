{-# LANGUAGE CPP #-}

-- | Translating Agda types to Haskell types. Used to ensure that imported
--   Haskell functions have the right type.

module Agda.Compiler.MAlonzo.HaskellTypes where

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

import Agda.Compiler.MAlonzo.Pragmas
import Agda.Compiler.MAlonzo.Misc
import Agda.Compiler.MAlonzo.Pretty

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
  let namedType = do
        -- For these builtin types, the type name (xhqn ...) refers to the
        -- generated, but unused, datatype and not the primitive type.
        nat  <- getBuiltinName builtinNat
        int  <- getBuiltinName builtinInteger
        bool <- getBuiltinName builtinBool
        case () of
          _ | Just x `elem` [nat, int] -> return "Integer"
            | Just x == bool           -> return "Bool"
            | otherwise                -> prettyShow <$> xhqn "T" x
  setCurrentRange d $ case d of
    Just HsDefn{} -> return hsUnit
    Just HsType{} -> namedType
    Just HsData{} -> namedType
    _             -> notAHaskellType (El Prop $ Def x [])

getHsVar :: Nat -> TCM HaskellCode
getHsVar i = hsVar <$> nameOfBV i

-- | Note that @Inf a b@, where @Inf@ is the INFINITY builtin, is
-- translated to @<translation of b>@ (assuming that all coinductive
-- builtins are defined).
--
-- Note that if @haskellType@ supported universe polymorphism then the
-- special treatment of INFINITY might not be needed.

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
        Def d es | Just d == (nameOfInf <$> kit) ->
          case es of
            [Apply a, Apply b] -> fromTerm (unArg b)
            _                  -> err
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

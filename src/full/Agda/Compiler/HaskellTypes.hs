{-# LANGUAGE CPP #-}

-- | Translating Agda types to Haskell types. Used to ensure that imported
--   Haskell functions have the right type.

module Agda.Compiler.HaskellTypes where

import Control.Applicative
import Control.Monad.Error
import Data.Char

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
-- import Agda.TypeChecking.Rules.Builtin.Coinduction
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free
import Agda.Utils.Monad
import Agda.Utils.Impossible

#include "../undefined.h"

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
hsVar x = "x" ++ concatMap encode (show x)
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

notAHaskellKind :: Type -> TCM a
notAHaskellKind a = do
  err <- fsep $ pwords "The type" ++ [prettyTCM a] ++
                pwords "cannot be translated to a Haskell kind."
  typeError $ GenericError $ show err

notAHaskellType :: Type -> TCM a
notAHaskellType a = do
  err <- fsep $ pwords "The type" ++ [prettyTCM a] ++
                pwords "cannot be translated to a Haskell type."
  typeError $ GenericError $ show err

getHsType :: QName -> TCM HaskellType
getHsType x = do
  d <- compiledHaskell . defCompiledRep <$> getConstInfo x
  case d of
    Just (HsType t)   -> return t
    Just (HsDefn t c) -> return hsUnit
    _                 -> notAHaskellType (El Prop $ Def x [])

getHsVar :: Nat -> TCM HaskellCode
getHsVar i = hsVar <$> nameOfBV i

isHaskellKind :: Type -> TCM Bool
isHaskellKind a =
  (const True <$> haskellKind a) `catchError` \_ -> return False

haskellKind :: Type -> TCM HaskellKind
haskellKind a = do
  a <- reduce a
  case unEl a of
    Sort _  -> return hsStar
    Pi a b  -> hsKFun <$> haskellKind (unDom a) <*> underAbstraction a b haskellKind
    Def d _ -> do
      d <- compiledHaskell . defCompiledRep <$> getConstInfo d
      case d of
        Just (HsType t) -> return hsStar
        _               -> notAHaskellKind a
    _       -> notAHaskellKind a

-- | Note that @Inf a b@, where @Inf@ is the INFINITY builtin, is
-- translated to @<translation of b>@ (assuming that all coinductive
-- builtins are defined).
--
-- Note that if @haskellType@ supported universe polymorphism then the
-- special treatment of INFINITY might not be needed.

haskellType :: Type -> TCM HaskellType
haskellType = liftTCM . fromType
  where
    fromArgs = mapM (fromTerm . unArg)
    fromType = fromTerm . unEl
    fromTerm v = do
      v   <- reduce v
      reportSLn "compile.haskell.type" 50 $ "toHaskellType " ++ show v
      kit <- liftTCM coinductionKit
      let err = notAHaskellType (El Prop v)
      case v of
        Var x args -> hsApp <$> getHsVar x <*> fromArgs args
        Def d args | Just d == (nameOfInf <$> kit) ->
          case args of
            [a, b] -> fromTerm (unArg b)
            _      -> err
        Def d args -> hsApp <$> getHsType d <*> fromArgs args
        Pi a b ->
          if isBinderUsed b  -- Andreas, 2012-04-03.  Q: could we rely on Abs/NoAbs instead of again checking freeness of variable?
          then underAbstraction a b $ \b ->
            hsForall <$> getHsVar 0 <*>
              (hsFun <$> fromType (unDom a) <*> fromType b)
          else hsFun <$> fromType (unDom a) <*> fromType (absApp b __IMPOSSIBLE__)
        Con c args -> hsApp <$> getHsType c <*> fromArgs args
        Lam{}      -> err
        Level{}    -> return hsUnit
        Lit{}      -> return hsUnit
        Sort{}     -> return hsUnit
        Shared p   -> fromTerm $ derefPtr p
        MetaV{}    -> err
        DontCare{} -> err

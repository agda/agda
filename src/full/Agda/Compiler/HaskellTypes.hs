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
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
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

notAHaskellKind :: MonadTCM tcm => Type -> tcm a
notAHaskellKind a = do
  err <- fsep $ pwords "The type" ++ [prettyTCM a] ++
                pwords "cannot be translated to a Haskell kind."
  typeError $ GenericError $ show err

notAHaskellType :: MonadTCM tcm => Type -> tcm a
notAHaskellType a = do
  err <- fsep $ pwords "The type" ++ [prettyTCM a] ++
                pwords "cannot be translated to a Haskell type."
  typeError $ GenericError $ show err

getHsType :: MonadTCM tcm => QName -> tcm HaskellType
getHsType x = do
  d <- theDef <$> getConstInfo x
  case d of
    Axiom{ axHsDef = Just (HsType t) } -> return t
    Datatype{ dataHsType = Just t }    -> return t
    _                                  -> notAHaskellType (El Prop $ Def x [])

getHsVar :: MonadTCM tcm => Nat -> tcm HaskellCode
getHsVar i = hsVar <$> nameOfBV i

isHaskellKind :: Type -> TCM Bool
isHaskellKind a =
  (const True <$> haskellKind a) `catchError` \_ -> return False

haskellKind :: MonadTCM tcm => Type -> tcm HaskellKind
haskellKind a = do
  a <- reduce a
  case unEl a of
    Sort _  -> return hsStar
    Pi a b  -> hsKFun <$> haskellKind (unArg a) <*> underAbstraction a b haskellKind
    Fun a b -> hsKFun <$> haskellKind (unArg a) <*> haskellKind b
    _       -> notAHaskellKind a

haskellType :: MonadTCM tcm => Type -> tcm HaskellType
haskellType = liftTCM . fromType
  where
    fromArgs = mapM (fromTerm . unArg)
    fromType = fromTerm . unEl
    fromTerm v = do
      v <- reduce v
      case ignoreBlocking v of
        Var x args -> hsApp <$> getHsVar x <*> fromArgs args
        Def d args -> hsApp <$> getHsType d <*> fromArgs args
        Fun a b    -> hsFun <$> fromType (unArg a) <*> fromType b
        Pi a b ->
          ifM (isHaskellKind $ unArg a)
          (underAbstraction a b $ \b -> do
              x <- getHsVar 0
              b <- fromType b
              return $ hsForall x $ hsFun "()" b
          )
          (if 0 `freeIn` absBody b
           then notAHaskellType (El Prop v)
           else hsFun <$> fromType (unArg a) <*> fromType (absApp b __IMPOSSIBLE__)
          )
        Con{}      -> notAHaskellType (El Prop v)
        Lam{}      -> notAHaskellType (El Prop v)
        Lit{}      -> notAHaskellType (El Prop v)
        Sort{}     -> notAHaskellType (El Prop v)
        MetaV{}    -> notAHaskellType (El Prop v)
        BlockedV{} -> __IMPOSSIBLE__




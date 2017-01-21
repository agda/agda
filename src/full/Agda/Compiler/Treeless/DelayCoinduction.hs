{-# LANGUAGE CPP #-}
-- | Inserts an additional lambda into all coinductive auxiliary definitions (== target type Inf XX). E.g.:
--
--   f : A -> B -> C -> Inf A
--   f = \a b c -> body
-- is converted to
--   f = \a b c _ -> body
--
-- Assumes that flat/sharp are implemented as follows:
--
-- flat = \x -> x
-- sharp = \x -> x ()

module Agda.Compiler.Treeless.DelayCoinduction where

import Control.Applicative

import Agda.Syntax.Internal (Type, telToList)
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Treeless

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Reduce ( instantiateFull, normalise )
import Agda.TypeChecking.Substitute hiding (underLambdas)
import Agda.TypeChecking.Telescope

import Agda.Compiler.Treeless.Subst

import Agda.Utils.Impossible

#include "undefined.h"

delayCoinduction :: TTerm -> Type -> TCM TTerm
delayCoinduction t ty = do
  kit <- coinductionKit
  case kit of
    Just kit -> transform kit t ty
    Nothing -> return t


transform :: CoinductionKit -> TTerm -> Type -> TCM TTerm
transform kit t ty = do
  isInf <- outputIsInf (Just kit) ty
  if isInf then do
      ty <- normalise ty
      TelV tel _ <- telView ty
      -- insert additional lambda
      return $ underLambdas (length $ telToList tel) (TLam . raise 1) t
    else
      return t


outputIsInf :: Maybe CoinductionKit -> Type -> TCM Bool
outputIsInf kit ty = do
  ty <- normalise ty
  tn <- getOutputTypeName ty
  case tn of
    OutputTypeName tn -> return $ Just tn == (nameOfInf <$> kit)
    _ -> return False


underLambdas :: Int -> (TTerm -> TTerm) -> TTerm -> TTerm
underLambdas n cont v = loop n v where
  loop 0 v = cont v
  loop n v = case v of
    TLam b -> TLam $ loop (n-1) b
    _       -> __IMPOSSIBLE__

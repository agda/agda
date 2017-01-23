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
-- sharp = \x -> x   -- delay
-- flat = \x -> x () -- force
--
-- NOTE: You may be tempted to forgo this transformation and instead implement sharp
-- as ``\x _ -> x`` . This does not work in strict languages. For example,
-- the following Agda code
--
-- data Stream : Set where
--   _::_ : Nat -> Inf Stream -> Stream
--
-- ones : Stream
-- ones = 1 :: (sharp ones)
--
-- will be compiled to
--
-- ones : Stream
-- ones = 1 :: sharp-0
-- sharp-0 : Inf Stream
-- sharp-0 = sharp ones
--
-- Evaluating ``ones`` in a strict language will evaluate ``sharp-0`` and thereby also the
-- recursive call to ``ones``. The evaluation of the tail of the stream is *not* delayed.
-- This transformation solves this by inserting a lambda around all expressions which
-- need to be delayed. This yields the following code, where ``sharp`` is assumed to be
-- the identity function:
--
-- ones = 1 :: sharp-0
-- sharp-0 = \_ -> sharp ones
--
--
-- This complication does not occur in lazy target languages.

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

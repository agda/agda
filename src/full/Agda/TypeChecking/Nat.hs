
module Agda.TypeChecking.Nat where

import Control.Applicative

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Monad.Builtin

data NatView = ClosedNat Integer
             | Plus Integer Term

natView :: MonadTCM tcm => Term -> tcm NatView
natView a = do
  Con suc []  <- primSuc
  Con zero [] <- primZero
  let view a = do
        a <- reduce a
        case a of
          Con s [Arg NotHidden a]
            | s == suc -> inc <$> view a
          Con z []
            | z == zero -> return $ ClosedNat 0
          _             -> return $ Plus 0 a
  view a
  where
    inc (ClosedNat n) = ClosedNat $ n + 1
    inc (Plus n a)    = Plus (n + 1) a


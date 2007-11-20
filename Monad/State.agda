
-- The state monad

module Monad.State where

open import Monad
open import Monad.Identity
open import Data.Product

StateT : Set -> (Set -> Set) -> Set -> Set
StateT S M A = S -> M (A × S)

StateTMonad : forall S {M} -> RawMonad M -> RawMonad (StateT S M)
StateTMonad s Mon = record
  { return = \x s -> return (x , s)
  ; bind   = \m f s -> m s >>= \r -> f (proj₁ r) (proj₂ r)
  }
  where
    open module M = MonadOps _ Mon

StateTMonadZero : forall S {M} -> RawMonadZero M -> RawMonadZero (StateT S M)
StateTMonadZero S Mon = record
  { monad = StateTMonad S (RawMonadZero.monad Mon)
  ; mzero = \s -> mzero
  }
  where
    open module M = MonadZeroOps _ Mon

StateTMonadPlus : forall S {M} -> RawMonadPlus M -> RawMonadPlus (StateT S M)
StateTMonadPlus S Mon = record
  { monadZero = StateTMonadZero S (RawMonadPlus.monadZero Mon)
  ; plus      = \m₁ m₂ s -> m₁ s ++ m₂ s
  }
  where
    open module M = MonadPlusOps _ Mon

State : Set -> Set -> Set
State S = StateT S Identity

StateMonad : (S : Set) -> RawMonad (State S)
StateMonad S = StateTMonad S IdentityMonad

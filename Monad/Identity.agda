
module Monad.Identity where

open import Monad

Identity : Set -> Set
Identity A = A

IdentityMonad : RawMonad Identity
IdentityMonad = record
  { return = \x -> x
  ; bind   = \x f -> f x
  }

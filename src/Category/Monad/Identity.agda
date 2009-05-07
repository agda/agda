------------------------------------------------------------------------
-- The identity monad
------------------------------------------------------------------------

module Category.Monad.Identity where

open import Category.Monad

Identity : Set → Set
Identity A = A

IdentityMonad : RawMonad Identity
IdentityMonad = record
  { return = λ x → x
  ; _>>=_  = λ x f → f x
  }

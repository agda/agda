------------------------------------------------------------------------
-- The identity monad
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Category.Monad.Identity where

open import Category.Monad

Identity : ∀ {f} → Set f → Set f
Identity A = A

IdentityMonad : ∀ {f} → RawMonad (Identity {f})
IdentityMonad = record
  { return = λ x → x
  ; _>>=_  = λ x f → f x
  }

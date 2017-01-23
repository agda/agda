------------------------------------------------------------------------
-- The Agda standard library
--
-- The identity functor
------------------------------------------------------------------------

module Category.Functor.Identity where

open import Category.Functor

Identity : ∀ {f} → Set f → Set f
Identity A = A

IdentityFunctor : ∀ {f} → RawFunctor (Identity {f})
IdentityFunctor = record
  { _<$>_ = λ x → x
  }

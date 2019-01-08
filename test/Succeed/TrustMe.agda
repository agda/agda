{-# OPTIONS --universe-polymorphism #-}

module TrustMe where

open import Common.Equality
open import Agda.Builtin.TrustMe

postulate
  A : Set
  x : A

eq : x ≡ x
eq = primTrustMe

evaluates-to-refl : sym (sym eq) ≡ eq
evaluates-to-refl = refl

{-# OPTIONS --universe-polymorphism #-}

module TrustMe where

open import Common.Equality
open import Agda.Builtin.TrustMe

postulate
  A   : Set
  x y : A

eq : x ≡ y
eq = primTrustMe

does-not-evaluate-to-refl : sym (sym eq) ≡ eq
does-not-evaluate-to-refl = refl

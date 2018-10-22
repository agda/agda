{-# OPTIONS --universe-polymorphism #-}

module TrustMe-with-doubly-indexed-equality where

open import Common.Level
open import Agda.Builtin.Equality
open import Agda.Builtin.TrustMe

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

postulate
  A : Set
  x : A

eq : x ≡ x
eq = primTrustMe

evaluates-to-refl : sym (sym eq) ≡ eq
evaluates-to-refl = refl

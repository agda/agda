{-# OPTIONS --universe-polymorphism #-}

module TrustMe where

open import Common.Equality

primitive
  primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y

postulate
  A : Set
  x : A

eq : x ≡ x
eq = primTrustMe

evaluates-to-refl : sym (sym eq) ≡ eq
evaluates-to-refl = refl

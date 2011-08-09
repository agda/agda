{-# OPTIONS --universe-polymorphism #-}

module TrustMe where

open import Common.Equality

primitive
  primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y

postulate
  A   : Set
  x y : A

eq : x ≡ y
eq = primTrustMe

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

does-not-evaluate-to-refl : sym (sym eq) ≡ eq
does-not-evaluate-to-refl = refl

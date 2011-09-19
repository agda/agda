{-# OPTIONS --universe-polymorphism #-}

module TrustMe-with-doubly-indexed-equality where

open import Common.Level

infix 4 _≡_

data _≡_ {a} {A : Set a} : A → A → Set a where
  refl : ∀ {x} → x ≡ x

{-# BUILTIN EQUALITY _≡_  #-}
{-# BUILTIN REFL     refl #-}

primitive
  primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y

postulate
  A : Set
  x : A

eq : x ≡ x
eq = primTrustMe

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

evaluates-to-refl : sym (sym eq) ≡ eq
evaluates-to-refl = refl

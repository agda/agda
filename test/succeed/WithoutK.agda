{-# OPTIONS --without-K --universe-polymorphism #-}

module WithoutK where

open import Common.Level

-- Propositional equality.

data _≡_ {A : Set} : A → A → Set where
  refl : ∀ x → x ≡ x

-- The J rule.

J : {A : Set} (P : {x y : A} → x ≡ y → Set) →
    (∀ x → P (refl x)) →
    ∀ {x y} (x≡y : x ≡ y) → P x≡y
J P p (refl x) = p x

-- Christine Paulin-Mohring's version of the J rule.

J′ : {A : Set} {x : A} (P : {y : A} → x ≡ y → Set) →
     P (refl x) →
     ∀ {y} (x≡y : x ≡ y) → P x≡y
J′ P p (refl x) = p

-- A variant of _≡_.

data _≡′_ {A : Set} (x : A) : A → Set where
  refl : x ≡′ x

-- We normalise before checking index well-formedness.

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x _ = x

id : {A : Set} {x y : A} → const x y ≡′ const y x → x ≡′ y
id refl = refl

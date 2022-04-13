{-# OPTIONS --cubical-compatible --universe-polymorphism #-}

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

-- We can handle more complicated indices as well.

data ⊥ : Set where

data Bool : Set where
  true false : Bool

true≢false : true ≡ false → ⊥
true≢false ()

data D : Set where
  c₀ : D
  c₂ : (i₁ i₂ : D) → D

f : ∀ {x y z} → x ≡ y → c₂ y c₀ ≡ c₂ c₀ z → x ≡ z
f x≡y (refl .(c₂ c₀ c₀)) = x≡y

-- The indices can contain literals.

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ    #-}

g : 2 ≡ 3 → 3 ≡ 5
g ()

h : ∀ {n} → 2 ≡ suc n → n ≡ 1
h (refl .2) = refl _

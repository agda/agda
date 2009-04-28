------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

module Relation.Binary.PropositionalEquality1 where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Propositional equality

infix 4 _≡₁_ _≢₁_

data _≡₁_ {a : Set₁} (x : a) : a → Set where
  refl : x ≡₁ x

-- Nonequality.

_≢₁_ : {a : Set₁} → a → a → Set
x ≢₁ y = ¬ x ≡₁ y

------------------------------------------------------------------------
-- Some properties

reflexive : ∀ {a} (x : a) → x ≡₁ x
reflexive _ = refl

sym : ∀ {a} {x y : a} → x ≡₁ y → y ≡₁ x
sym refl = refl

trans : ∀ {a} {x y z : a} → x ≡₁ y → y ≡₁ z → x ≡₁ z
trans refl refl = refl

subst : {a b : Set} → a ≡₁ b → a → b
subst refl x = x

cong : ∀ {a b} (f : a → b) → ∀ {x y} → x ≡₁ y → f x ≡₁ f y
cong _ refl = refl

cong₂ : ∀ {a b c} (f : a → b → c) →
        ∀ {x₁ x₂ y₁ y₂} → x₁ ≡₁ x₂ → y₁ ≡₁ y₂ → f x₁ y₁ ≡₁ f x₂ y₂
cong₂ _ refl refl = refl

cong₀₁ : ∀ {a b} (f : a → b) → ∀ {x y} → x ≡ y → f x ≡₁ f y
cong₀₁ _ refl = refl

cong₁₀ : ∀ {a b} (f : a → b) → ∀ {x y} → x ≡₁ y → f x ≡ f y
cong₁₀ _ refl = refl

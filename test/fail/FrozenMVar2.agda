-- Andreas, 2011-04-11 adapted from Data.Nat.Properties

{-# OPTIONS --universe-polymorphism #-}

module FrozenMVar2 where

open import Imports.Level

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

cong : ∀ {a b} {A : Set a} {B : Set b}
       (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

Rel : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Rel A ℓ = A → A → Set ℓ

Op₂ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₂ A = A → A → A

module FunctionProperties
         {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

  Associative : Op₂ A → Set _
  Associative _∙_ = ∀ x y z → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))

open FunctionProperties _≡_  -- THIS produces frozen metas

data ℕ : Set where
  zℕ : ℕ
  sℕ : (n : ℕ) → ℕ

infixl 6 _+_

_+_ : ℕ → ℕ → ℕ
zℕ   + n = n
sℕ m + n = sℕ (m + n)

+-assoc : Associative _+_
-- +-assoc : ∀ x y z -> ((x + y) + z) ≡ (x + (y + z)) -- this works
+-assoc zℕ     _ _ = refl
+-assoc (sℕ m) n o = cong sℕ (+-assoc m n o)
-- Due to a frozen meta we get:
-- Type mismatch when checking that the pattern zℕ has type _95

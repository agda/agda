-- Andreas, 2011-04-11 adapted from Data.Nat.Properties

module FrozenMVar2 where

open import Common.Level
open import Common.Equality

Rel : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
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

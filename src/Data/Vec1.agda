------------------------------------------------------------------------
-- Vectors parameterised on types in Set₁
------------------------------------------------------------------------

-- I want universe polymorphism.

module Data.Vec1 where

infixr 5 _∷_

open import Data.Nat
open import Data.Vec using (Vec; []; _∷_)
open import Data.Fin

------------------------------------------------------------------------
-- The type

data Vec₁ (a : Set₁) : ℕ → Set₁ where
  []  : Vec₁ a zero
  _∷_ : ∀ {n} (x : a) (xs : Vec₁ a n) → Vec₁ a (suc n)

------------------------------------------------------------------------
-- Some operations

map : ∀ {a b n} → (a → b) → Vec₁ a n → Vec₁ b n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

map₀₁ : ∀ {a b n} → (a → b) → Vec a n → Vec₁ b n
map₀₁ f []       = []
map₀₁ f (x ∷ xs) = f x ∷ map₀₁ f xs

map₁₀ : ∀ {a b n} → (a → b) → Vec₁ a n → Vec b n
map₁₀ f []       = []
map₁₀ f (x ∷ xs) = f x ∷ map₁₀ f xs

lookup : ∀ {a n} → Fin n → Vec₁ a n → a
lookup zero    (x ∷ xs) = x
lookup (suc i) (x ∷ xs) = lookup i xs

------------------------------------------------------------------------
-- Bounded vectors (inefficient, concrete implementation)
------------------------------------------------------------------------

-- Vectors of a specified maximum length.

{-# OPTIONS --universe-polymorphism #-}
module Data.BoundedVec.Inefficient where

open import Data.Nat
open import Data.List

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

data BoundedVec {ℓ} (a : Set ℓ) : ℕ → Set ℓ where
  []  : ∀ {n} → BoundedVec a n
  _∷_ : ∀ {n} (x : a) (xs : BoundedVec a n) → BoundedVec a (suc n)

------------------------------------------------------------------------
-- Increasing the bound

-- Note that this operation is linear in the length of the list.

↑ : ∀ {ℓ n} {a : Set ℓ} → BoundedVec a n → BoundedVec a (suc n)
↑ []       = []
↑ (x ∷ xs) = x ∷ ↑ xs

------------------------------------------------------------------------
-- Conversions

fromList : ∀ {ℓ} {a : Set ℓ} → (xs : List a) → BoundedVec a (length xs)
fromList []       = []
fromList (x ∷ xs) = x ∷ fromList xs

toList : ∀ {ℓ n} {a : Set ℓ} → BoundedVec a n → List a
toList []       = []
toList (x ∷ xs) = x ∷ toList xs

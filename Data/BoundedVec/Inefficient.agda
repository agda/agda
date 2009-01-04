------------------------------------------------------------------------
-- Bounded vectors (inefficient, concrete implementation)
------------------------------------------------------------------------

-- Vectors of a specified maximum length.

module Data.BoundedVec.Inefficient where

open import Data.Nat
open import Data.List

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

data BoundedVec (a : Set) : ℕ → Set where
  []  : ∀ {n} → BoundedVec a n
  _∷_ : ∀ {n} (x : a) (xs : BoundedVec a n) → BoundedVec a (suc n)

------------------------------------------------------------------------
-- Increasing the bound

-- Note that this operation is linear in the length of the list.

↑ : ∀ {a n} → BoundedVec a n → BoundedVec a (suc n)
↑ []       = []
↑ (x ∷ xs) = x ∷ ↑ xs

------------------------------------------------------------------------
-- Conversions

fromList : ∀ {a} → (xs : List a) → BoundedVec a (length xs)
fromList []       = []
fromList (x ∷ xs) = x ∷ fromList xs

toList : ∀ {a n} → BoundedVec a n → List a
toList []       = []
toList (x ∷ xs) = x ∷ toList xs

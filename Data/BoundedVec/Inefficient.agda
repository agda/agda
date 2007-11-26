------------------------------------------------------------------------
-- Bounded vectors (inefficient, concrete implementation)
------------------------------------------------------------------------

-- Vectors of a specified maximum length.

module Data.BoundedVec.Inefficient where

open import Data.Nat
open import Data.List renaming ([] to []l; _∷_ to _∷l_)

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

data BoundedVec (a : Set) : ℕ -> Set where
  []  : forall {n} -> BoundedVec a n
  _∷_ : forall {n} -> a -> BoundedVec a n -> BoundedVec a (suc n)

------------------------------------------------------------------------
-- Increasing the bound

-- Note that this operation is linear in the length of the list.

↑ : forall {a n} -> BoundedVec a n -> BoundedVec a (suc n)
↑ []       = []
↑ (x ∷ xs) = x ∷ ↑ xs

------------------------------------------------------------------------
-- Conversions

fromList : forall {a} -> (xs : [ a ]) -> BoundedVec a (length xs)
fromList []l       = []
fromList (x ∷l xs) = x ∷ fromList xs

toList : forall {a n} -> BoundedVec a n -> [ a ]
toList []       = []l
toList (x ∷ xs) = x ∷l toList xs

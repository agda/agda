------------------------------------------------------------------------
-- Vectors parameterised on types in Set1
------------------------------------------------------------------------

-- I want universe polymorphism.

module Data.Vec1 where

infixr 5 _∷_

open import Data.Nat
open import Data.Vec

------------------------------------------------------------------------
-- The type

data Vec₁ (a : Set1) : ℕ -> Set1 where
  []  : Vec₁ a zero
  _∷_ : forall {n} (x : a) (xs : Vec₁ a n) -> Vec₁ a (suc n)

------------------------------------------------------------------------
-- Some operations

map₀₁ : forall {a b n} -> (a -> b) -> Vec a n -> Vec₁ b n
map₀₁ f []       = []
map₀₁ f (x ∷ xs) = f x ∷ map₀₁ f xs

------------------------------------------------------------------------
-- Vectors (some core definitions)
------------------------------------------------------------------------

-- The definitions in this file are reexported by Data.Vec.

module Data.Vec.Core where

infixr 5 _∷_

open import Data.Nat
open import Data.Fin.Core

------------------------------------------------------------------------
-- The type

data Vec (a : Set) : ℕ -> Set where
  []  : Vec a zero
  _∷_ : forall {n} -> a -> Vec a n -> Vec a (suc n)

------------------------------------------------------------------------
-- Some operations

lookup : forall {a n} -> Fin n -> Vec a n -> a
lookup fz     (x ∷ xs) = x
lookup (fs i) (x ∷ xs) = lookup i xs

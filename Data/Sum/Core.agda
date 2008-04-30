------------------------------------------------------------------------
-- Sums (disjoint unions)
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Data.Sum.

module Data.Sum.Core where

infixr 1 _⊎_

data _⊎_ (a b : Set) : Set where
  inj₁ : a -> a ⊎ b
  inj₂ : b -> a ⊎ b

------------------------------------------------------------------------
-- Nullary relations
------------------------------------------------------------------------

module Relation.Nullary where

open import Logic

------------------------------------------------------------------------
-- Properties

-- Decidable property.

data Dec (P : Set) : Set where
  yes : P   -> Dec P
  no  : ¬ P -> Dec P

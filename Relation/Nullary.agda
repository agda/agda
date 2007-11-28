------------------------------------------------------------------------
-- Nullary relations
------------------------------------------------------------------------

module Relation.Nullary where

open import Logic

------------------------------------------------------------------------
-- Properties of nullary relations

-- P is decidable.

data Dec (P : Set) : Set where
  yes : P   -> Dec P
  no  : ¬ P -> Dec P

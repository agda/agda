------------------------------------------------------------------------
-- Nullary relations
------------------------------------------------------------------------

module Relation.Nullary where

open import Logic
open import Data.Unit.Core
open import Data.Bool.Core

------------------------------------------------------------------------
-- Properties of nullary relations

-- P is decidable.

data Dec (P : Set) : Set where
  yes : P   -> Dec P
  no  : ¬ P -> Dec P

decToBool : forall {P} -> Dec P -> Bool
decToBool (yes _) = true
decToBool (no  _) = false

True : forall {P} -> Dec P -> Set
True (yes _) = ⊤
True (no _)  = ⊥

False : forall {P} -> Dec P -> Set
False (yes _) = ⊥
False (no _)  = ⊤

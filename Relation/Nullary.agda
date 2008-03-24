------------------------------------------------------------------------
-- Nullary relations
------------------------------------------------------------------------

module Relation.Nullary where

open import Logic
open import Data.Unit.Core
open import Data.Bool.Core

------------------------------------------------------------------------
-- Decidable relations

data Dec (P : Set) : Set where
  yes : P   -> Dec P
  no  : ¬ P -> Dec P

decToBool : forall {P} -> Dec P -> Bool
decToBool (yes _) = true
decToBool (no  _) = false

True : forall {P} -> Dec P -> Set
True Q = T (decToBool Q)

False : forall {P} -> Dec P -> Set
False Q = T (not (decToBool Q))

witnessToTruth : forall {P} {Q : Dec P} -> True Q -> P
witnessToTruth {Q = yes p} _  = p
witnessToTruth {Q = no  _} ()

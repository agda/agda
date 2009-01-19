------------------------------------------------------------------------
-- Operations on and properties of decidable relations
------------------------------------------------------------------------

module Relation.Nullary.Decidable where

open import Relation.Nullary
open import Data.Bool

decToBool : ∀ {P} → Dec P → Bool
decToBool (yes _) = true
decToBool (no  _) = false

True : ∀ {P} → Dec P → Set
True Q = T (decToBool Q)

False : ∀ {P} → Dec P → Set
False Q = T (not (decToBool Q))

witnessToTruth : ∀ {P} {Q : Dec P} → True Q → P
witnessToTruth {Q = yes p} _  = p
witnessToTruth {Q = no  _} ()

------------------------------------------------------------------------
-- Operations on and properties of decidable relations
------------------------------------------------------------------------

module Relation.Nullary.Decidable where

open import Relation.Nullary
open import Data.Function
open import Data.Bool
open import Data.Product using (_,_)

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

map : ∀ {P Q} → P ⇔ Q → Dec P → Dec Q
map (to , from) (yes p) = yes (to p)
map (to , from) (no ¬p) = no (¬p ∘ from)

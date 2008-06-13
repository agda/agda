------------------------------------------------------------------------
-- Nullary relations
------------------------------------------------------------------------

-- Some operations on/properties of nullary relations, i.e. sets.

module Relation.Nullary where

open import Data.Product
open import Data.Bool
open import Data.Empty

open import Relation.Nullary.Core public

------------------------------------------------------------------------
-- Equivalence

infix 4 _⇔_

_⇔_ : Set -> Set -> Set
P ⇔ Q = (P -> Q) × (Q -> P)

------------------------------------------------------------------------
-- Negation

contradiction : forall {P whatever} -> P -> ¬ P -> whatever
contradiction p np = ⊥-elim (np p)

contravariant : forall {P Q} -> (P -> Q) -> ¬ Q -> ¬ P
contravariant f ¬q p = contradiction (f p) ¬q

map-¬¬ : forall {P Q} -> (P -> Q) -> ¬ (¬ P) -> ¬ (¬ Q)
map-¬¬ f = contravariant (contravariant f)

------------------------------------------------------------------------
-- Decidable relations

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

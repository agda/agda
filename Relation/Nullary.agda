------------------------------------------------------------------------
-- Nullary relations
------------------------------------------------------------------------

-- Some operations on/properties of nullary relations, i.e. sets.

module Relation.Nullary where

open import Data.Unit.Core
open import Data.Bool.Core
open import Data.Empty

------------------------------------------------------------------------
-- Negation

infix 3 ¬_

¬_ : Set -> Set
¬ P = P -> ⊥

contradiction : forall {P whatever} -> P -> ¬ P -> whatever
contradiction p np = ⊥-elim (np p)

contravariant : forall {P Q} -> (P -> Q) -> ¬ Q -> ¬ P
contravariant f ¬q p = contradiction (f p) ¬q

map-¬¬ : forall {P Q} -> (P -> Q) -> ¬ (¬ P) -> ¬ (¬ Q)
map-¬¬ f = contravariant (contravariant f)

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

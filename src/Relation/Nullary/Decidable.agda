------------------------------------------------------------------------
-- Operations on and properties of decidable relations
------------------------------------------------------------------------

module Relation.Nullary.Decidable where

open import Data.Empty
open import Data.Function
open import Data.Bool
open import Data.Product hiding (map)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

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
map eq (yes p) = yes (proj₁ eq p)
map eq (no ¬p) = no (¬p ∘ proj₂ eq)

fromYes : ∀ {P} → P → Dec P → P
fromYes _ (yes p) = p
fromYes p (no ¬p) = ⊥-elim (¬p p)

fromYes-map-commute :
  ∀ {P Q p q} (eq : P ⇔ Q) (d : Dec P) →
  fromYes q (map eq d) ≡ proj₁ eq (fromYes p d)
fromYes-map-commute         _ (yes p) = refl
fromYes-map-commute {p = p} _ (no ¬p) = ⊥-elim (¬p p)

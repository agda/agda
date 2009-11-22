------------------------------------------------------------------------
-- Operations on and properties of decidable relations
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Nullary.Decidable where

open import Data.Empty
open import Data.Function
open import Data.Bool
open import Data.Product hiding (map)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

decToBool : ∀ {p} {P : Set p} → Dec P → Bool
decToBool (yes _) = true
decToBool (no  _) = false

True : ∀ {p} {P : Set p} → Dec P → Set
True Q = T (decToBool Q)

False : ∀ {p} {P : Set p} → Dec P → Set
False Q = T (not (decToBool Q))

-- Gives a witness to the "truth".

toWitness : ∀ {p} {P : Set p} {Q : Dec P} → True Q → P
toWitness {Q = yes p} _  = p
toWitness {Q = no  _} ()

-- Establishes a "truth", given a witness.

fromWitness : ∀ {p} {P : Set p} {Q : Dec P} → P → True Q
fromWitness {Q = yes p} = const _
fromWitness {Q = no ¬p} = ¬p

map : ∀ {p q} {P : Set p} {Q : Set q} → P ⇔ Q → Dec P → Dec Q
map eq (yes p) = yes (proj₁ eq p)
map eq (no ¬p) = no (¬p ∘ proj₂ eq)

fromYes : ∀ {p} {P : Set p} → P → Dec P → P
fromYes _ (yes p) = p
fromYes p (no ¬p) = ⊥-elim (¬p p)

fromYes-map-commute :
  ∀ {p q} {P : Set p} {Q : Set q} {x y} (eq : P ⇔ Q) (d : Dec P) →
  fromYes y (map eq d) ≡ proj₁ eq (fromYes x d)
fromYes-map-commute         _ (yes p) = refl
fromYes-map-commute {x = p} _ (no ¬p) = ⊥-elim (¬p p)

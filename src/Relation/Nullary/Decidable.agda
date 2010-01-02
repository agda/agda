------------------------------------------------------------------------
-- Operations on and properties of decidable relations
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Nullary.Decidable where

open import Data.Empty
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using (_⇔_; equivalent; module Equivalent)
open import Data.Bool
open import Data.Product hiding (map)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

⌊_⌋ : ∀ {p} {P : Set p} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false

True : ∀ {p} {P : Set p} → Dec P → Set
True Q = T ⌊ Q ⌋

False : ∀ {p} {P : Set p} → Dec P → Set
False Q = T (not ⌊ Q ⌋)

-- Gives a witness to the "truth".

toWitness : ∀ {p} {P : Set p} {Q : Dec P} → True Q → P
toWitness {Q = yes p} _  = p
toWitness {Q = no  _} ()

-- Establishes a "truth", given a witness.

fromWitness : ∀ {p} {P : Set p} {Q : Dec P} → P → True Q
fromWitness {Q = yes p} = const _
fromWitness {Q = no ¬p} = ¬p

map : ∀ {p q} {P : Set p} {Q : Set q} → P ⇔ Q → Dec P → Dec Q
map P⇔Q (yes p) = yes (Equivalent.to P⇔Q ⟨$⟩ p)
map P⇔Q (no ¬p) = no (¬p ∘ _⟨$⟩_ (Equivalent.from P⇔Q))

map′ : ∀ {p q} {P : Set p} {Q : Set q} →
       (P → Q) → (Q → P) → Dec P → Dec Q
map′ P→Q Q→P = map (equivalent P→Q Q→P)

fromYes : ∀ {p} {P : Set p} → P → Dec P → P
fromYes _ (yes p) = p
fromYes p (no ¬p) = ⊥-elim (¬p p)

fromYes-map-commute :
  ∀ {p q} {P : Set p} {Q : Set q} {x y} (P⇔Q : P ⇔ Q) (d : Dec P) →
  fromYes y (map P⇔Q d) ≡ Equivalent.to P⇔Q ⟨$⟩ fromYes x d
fromYes-map-commute         _ (yes p) = refl
fromYes-map-commute {x = p} _ (no ¬p) = ⊥-elim (¬p p)

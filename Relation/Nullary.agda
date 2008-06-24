------------------------------------------------------------------------
-- Nullary relations
------------------------------------------------------------------------

-- Some operations on/properties of nullary relations, i.e. sets.

module Relation.Nullary where

open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Function
open import Data.Bool

open import Relation.Nullary.Core public

------------------------------------------------------------------------
-- Equivalence

infix 4 _⇔_

_⇔_ : Set -> Set -> Set
P ⇔ Q = (P -> Q) × (Q -> P)

------------------------------------------------------------------------
-- Negation

contradiction : forall {P whatever} -> P -> ¬ P -> whatever
contradiction p ¬p = ⊥-elim (¬p p)

contravariant : forall {P Q} -> (P -> Q) -> ¬ Q -> ¬ P
contravariant f ¬q p = contradiction (f p) ¬q

-- Note also the following use of flip:

private
  note : forall {P Q} -> (P -> ¬ Q) -> Q -> ¬ P
  note = flip

-- And the following use of contradiction:

private
  add-¬¬ : {P : Set} -> P -> ¬ ¬ P
  add-¬¬ = contradiction

map-¬¬ : forall {P Q} -> (P -> Q) -> ¬ ¬ P -> ¬ ¬ Q
map-¬¬ f = contravariant (contravariant f)

push-¬¬ : {P : Set} {Q : P -> Set} ->
          ¬ ¬ ((x : P) -> Q x) -> (x : P) -> ¬ ¬ Q x
push-¬¬ ¬¬P⟶Q P ¬Q = ¬¬P⟶Q (\P⟶Q -> ¬Q (P⟶Q P))

drop-¬¬ : {P : Set} -> ¬ ¬ ¬ P -> ¬ P
drop-¬¬ ¬¬¬P P = ¬¬¬P (\ ¬P -> ¬P P)

drop-¬¬-Dec : {P : Set} -> Dec P -> ¬ ¬ P -> P
drop-¬¬-Dec (yes p) ¬¬p = p
drop-¬¬-Dec (no ¬p) ¬¬p = ⊥-elim (¬¬p ¬p)

-- A double-negation-translated variant of excluded middle.

excluded-middle : (P : Set) -> ¬ ¬ Dec P
excluded-middle P ¬h = ¬h (no (\p -> ¬h (yes p)))

-- Replace Q by ⊥ and simplify to get a double-negation-translated
-- variant of reductio ad absurdum.

reductio-ad-absurdum-⊎ : {P Q : Set} -> (¬ P -> Q) -> ¬ ¬ (P ⊎ Q)
reductio-ad-absurdum-⊎ {P} {Q} f hyp =
  excluded-middle P (hyp ∘ helper)
  where
  helper : Dec P -> P ⊎ Q
  helper (yes p) = inj₁ p
  helper (no ¬p) = inj₂ (f ¬p)

∃⟶¬∀¬ : {A : Set} {P : A -> Set} ->
        ∃ P -> ¬ (forall x -> ¬ P x)
∃⟶¬∀¬ = flip Σ-uncurry

∀⟶¬∃¬ : {A : Set} {P : A -> Set} ->
        (forall x -> P x) -> ¬ ∃ \x -> ¬ P x
∀⟶¬∃¬ ∀xPx (x , ¬Px) = ¬Px (∀xPx x)

¬∃⟶∀¬ : {A : Set} {P : A -> Set} ->
        ¬ ∃ (\x -> P x) -> forall x -> ¬ P x
¬∃⟶∀¬ = Σ-curry

∀¬⟶¬∃ : {A : Set} {P : A -> Set} ->
        (forall x -> ¬ P x) -> ¬ ∃ (\x -> P x)
∀¬⟶¬∃ = Σ-uncurry

∃¬⟶¬∀ : {A : Set} {P : A -> Set} ->
        ∃ (\x -> ¬ P x) -> ¬ (forall x -> P x)
∃¬⟶¬∀ = flip ∀⟶¬∃¬

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

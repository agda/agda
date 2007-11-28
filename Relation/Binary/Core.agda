------------------------------------------------------------------------
-- Properties of homogeneous binary relations
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Relation.Binary.

module Relation.Binary.Core where

open import Logic
open import Data.Product
open import Data.Sum
open import Data.Function
open import Relation.Nullary

------------------------------------------------------------------------
-- Homogeneous binary relations

Rel : Set -> Set1
Rel a = a -> a -> Set

------------------------------------------------------------------------
-- Simple properties of binary relations

-- Reflexivity is expressed in terms of an underlying, more "basic"
-- equality, which could for instance be _≡_.

Reflexive : {a : Set} -> (_≈_ _∼_ : Rel a) -> Set
Reflexive _≈_ _∼_ = forall {x y} -> x ≈ y -> x ∼ y

-- The same applies to irreflexivity.

Irreflexive : {a : Set} -> (_≈_ _<_ : Rel a) -> Set
Irreflexive _≈_ _<_ = forall {x y} -> x ≈ y -> ¬ (x < y)

Symmetric : {a : Set} -> Rel a -> Set
Symmetric _∼_ = forall {x y} -> x ∼ y -> y ∼ x

Transitive : {a : Set} -> Rel a -> Set
Transitive _∼_ = forall {x y z} -> x ∼ y -> y ∼ z -> x ∼ z

Antisymmetric : {a : Set} -> (_≈_ _≤_ : Rel a) -> Set
Antisymmetric _≈_ _≤_ = forall {x y} -> x ≤ y -> y ≤ x -> x ≈ y

Asymmetric : {a : Set} -> (_<_ : Rel a) -> Set
Asymmetric _<_ = forall {x y} -> x < y -> ¬ (y < x)

_Respects_ : {a : Set} -> Rel a -> (a -> Set) -> Set
_∼_ Respects P = forall {x y} -> x ∼ y -> P x -> P y

_Respects₂_ : {a : Set} -> Rel a -> Rel a -> Set
∼ Respects₂ P =
  (forall {x} -> ∼ Respects (P x)      ) ×
  (forall {y} -> ∼ Respects (flip₁ P y))

Substitutive : {a : Set} -> Rel a -> Set1
Substitutive {a} ∼ = (P : a -> Set) -> ∼ Respects P

_Preserves_→_ : forall {a₁ a₂} -> (a₁ -> a₂) -> Rel a₁ -> Rel a₂ -> Set
f Preserves _∼₁_ → _∼₂_ = forall {x y} -> x ∼₁ y -> f x ∼₂ f y

_Preserves₂_→_→_
  :  forall {a₁ a₂ a₃}
  -> (a₁ -> a₂ -> a₃) -> Rel a₁ -> Rel a₂ -> Rel a₃ -> Set
_+_ Preserves₂ _∼₁_ → _∼₂_ → _∼₃_ =
  forall {x y u v} -> x ∼₁ y -> u ∼₂ v -> (x + u) ∼₃ (y + v)

Congruential : ({a : Set} -> Rel a) -> Set1
Congruential ∼ = forall {a b} -> (f : a -> b) -> f Preserves ∼ → ∼

Congruential₂ : ({a : Set} -> Rel a) -> Set1
Congruential₂ ∼ =
  forall {a b c} -> (f : a -> b -> c) -> f Preserves₂ ∼ → ∼ → ∼

Decidable : {a : Set} -> Rel a -> Set
Decidable _∼_ = forall x y -> Dec (x ∼ y)

Total : {a : Set} -> Rel a -> Set
Total _∼_ = forall x y -> (x ∼ y) ⊎ (y ∼ x)

data Tri (a b c : Set) : Set where
  Tri₁ :   a -> ¬ b -> ¬ c -> Tri a b c
  Tri₂ : ¬ a ->   b -> ¬ c -> Tri a b c
  Tri₃ : ¬ a -> ¬ b ->   c -> Tri a b c

Trichotomous : {a : Set} -> Rel a -> Rel a -> Set
Trichotomous _≈_ _<_ = forall x y -> Tri (x < y) (x ≈ y) (x > y)
  where _>_ = flip₁ _<_

-- Is there any point with these synonyms?

Monotone
  :  forall {a₁} -> (≤₁ : Rel a₁)
  -> forall {a₂} -> (≤₂ : Rel a₂)
  -> (a₁ -> a₂) -> Set
Monotone ≤₁ ≤₂ f = f Preserves ≤₁ → ≤₂

Monotone₂
  :  forall {a₁} -> (≤₁ : Rel a₁)
  -> forall {a₂} -> (≤₂ : Rel a₂)
  -> forall {a₃} -> (≤₃ : Rel a₃)
  -> (a₁ -> a₂ -> a₃) -> Set
Monotone₂ ≤₁ ≤₂ ≤₃ • = • Preserves₂ ≤₁ → ≤₂ → ≤₃

------------------------------------------------------------------------
-- Equivalence relations

-- One could presumably define equivalence relations in terms of
-- preorders. However, the preorders of this library are defined in
-- terms of an underlying equivalence relation (used to define
-- reflexivity; note that this underlying equality is hard-wired to
-- _≡_ in the definition of IsEquivalence).

record IsEquivalence {a : Set} (_≈_ : Rel a) : Set where
  refl  : Reflexive _≡_ _≈_
  sym   : Symmetric _≈_
  trans : Transitive _≈_

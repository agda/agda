------------------------------------------------------------------------
-- Properties of homogeneous binary relations
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Relation.Binary or Relation.Binary.PropositionalEquality.

module Relation.Binary.Core where

open import Data.Product
open import Data.Sum
open import Data.Function
open import Data.Unit.Core
open import Data.Empty
open import Relation.Nullary.Core

------------------------------------------------------------------------
-- Homogeneous binary relations

Rel : Set -> Set1
Rel a = a -> a -> Set

------------------------------------------------------------------------
-- Some simple relations

-- Constant relations.

Const : forall {a} -> Set -> Rel a
Const I = \_ _ -> I

-- The universally true relation.

Always : forall {a} -> Rel a
Always = Const ⊤

-- The universally false relation.

Never : forall {a} -> Rel a
Never = Const ⊥

------------------------------------------------------------------------
-- Propositional equality

infix 4 _≡_ _≢_

data _≡_ {a : Set} (x : a) : a -> Set where
  ≡-refl : x ≡ x

-- Nonequality.

_≢_ : {a : Set} -> a -> a -> Set
x ≢ y = ¬ x ≡ y

------------------------------------------------------------------------
-- Simple properties of binary relations

infixr 4 _⇒_ _=[_]⇒_

-- Implication/containment. Could also be written ⊆.

_⇒_ : forall {a} -> Rel a -> Rel a -> Set
P ⇒ Q = forall {i j} -> P i j -> Q i j

-- Generalised implication. If P ≡ Q it can be read as "f preserves
-- P".

_=[_]⇒_ : forall {a b} -> Rel a -> (a -> b) -> Rel b -> Set
P =[ f ]⇒ Q = P ⇒ (Q on₁ f)

-- A synonym, along with a binary variant.

_Preserves_→_ : forall {a₁ a₂} -> (a₁ -> a₂) -> Rel a₁ -> Rel a₂ -> Set
f Preserves P → Q = P =[ f ]⇒ Q

_Preserves₂_→_→_
  :  forall {a₁ a₂ a₃}
  -> (a₁ -> a₂ -> a₃) -> Rel a₁ -> Rel a₂ -> Rel a₃ -> Set
_+_ Preserves₂ P → Q → R =
  forall {x y u v} -> P x y -> Q u v -> R (x + u) (y + v)

-- Reflexivity of _∼_ can be expressed as _≈_ ⇒ _∼_, for some
-- underlying equality _≈_. However, the following variant is often
-- easier to use.

Reflexive : {a : Set} -> (_∼_ : Rel a) -> Set
Reflexive _∼_ = forall {x} -> x ∼ x

-- Irreflexivity is defined using an underlying equality.

Irreflexive : {a : Set} -> (_≈_ _<_ : Rel a) -> Set
Irreflexive _≈_ _<_ = forall {x y} -> x ≈ y -> ¬ (x < y)

-- Generalised symmetry.

Sym : forall {a} -> Rel a -> Rel a -> Set
Sym P Q = P ⇒ flip₁ Q

Symmetric : {a : Set} -> Rel a -> Set
Symmetric _∼_ = Sym _∼_ _∼_

-- Generalised transitivity.

Trans : forall {a} -> Rel a -> Rel a -> Rel a -> Set
Trans P Q R = forall {i j k} -> P i j -> Q j k -> R i k

Transitive : {a : Set} -> Rel a -> Set
Transitive _∼_ = Trans _∼_ _∼_ _∼_

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
  tri< :   a -> ¬ b -> ¬ c -> Tri a b c
  tri≈ : ¬ a ->   b -> ¬ c -> Tri a b c
  tri> : ¬ a -> ¬ b ->   c -> Tri a b c

Trichotomous : {a : Set} -> Rel a -> Rel a -> Set
Trichotomous _≈_ _<_ = forall x y -> Tri (x < y) (x ≈ y) (x > y)
  where _>_ = flip₁ _<_

record NonEmpty {I : Set} (T : Rel I) : Set where
  field
    i     : I
    j     : I
    proof : T i j

nonEmpty : forall {I} {T : Rel I} {i j} -> T i j -> NonEmpty T
nonEmpty p = record { i = _; j = _; proof = p }

------------------------------------------------------------------------
-- Equivalence relations

-- The preorders of this library are defined in terms of an underlying
-- equivalence relation, and hence equivalence relations are not
-- defined in terms of preorders.

record IsEquivalence {a : Set} (_≈_ : Rel a) : Set where
  field
    refl  : Reflexive _≈_
    sym   : Symmetric _≈_
    trans : Transitive _≈_

  reflexive : _≡_ ⇒ _≈_
  reflexive ≡-refl = refl

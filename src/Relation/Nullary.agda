------------------------------------------------------------------------
-- Operations on nullary relations (like negation and decidability)
------------------------------------------------------------------------

-- Some operations on/properties of nullary relations, i.e. sets.

module Relation.Nullary where

open import Data.Product
import Relation.Nullary.Core as Core
open import Relation.Binary
open import Relation.Binary.FunctionSetoid
import Relation.Binary.EqReasoning as EqReasoning

------------------------------------------------------------------------
-- Negation

open Core public using (¬_)

------------------------------------------------------------------------
-- Equivalence

infix 3 _⇔_

_⇔_ : Set → Set → Set
P ⇔ Q = (P → Q) × (Q → P)

------------------------------------------------------------------------
-- Decidable relations

open Core public using (Dec; yes; no)

------------------------------------------------------------------------
-- Injections

Injective : ∀ {A B} → A ⟶ B → Set
Injective {A} {B} f = ∀ {x y} → f ⟨$⟩ x ≈₂ f ⟨$⟩ y → x ≈₁ y
  where
  open Setoid A renaming (_≈_ to _≈₁_)
  open Setoid B renaming (_≈_ to _≈₂_)

_LeftInverseOf_ : ∀ {A B} → B ⟶ A → A ⟶ B → Set
_LeftInverseOf_ {A} f g = ∀ x → f ⟨$⟩ (g ⟨$⟩ x) ≈₁ x
  where open Setoid A renaming (_≈_ to _≈₁_)

record Injection (From To : Setoid) : Set where
  field
    to        : From ⟶ To
    injective : Injective to

record LeftInverse (From To : Setoid) : Set where
  field
    to           : From ⟶ To
    from         : To ⟶ From
    left-inverse : from LeftInverseOf to

  open Setoid      From
  open EqReasoning From

  injective : Injective to
  injective {x} {y} eq = begin
    x                    ≈⟨ sym (left-inverse x) ⟩
    from ⟨$⟩ (to ⟨$⟩ x)  ≈⟨ pres from eq ⟩
    from ⟨$⟩ (to ⟨$⟩ y)  ≈⟨ left-inverse y ⟩
    y                    ∎

  injection : Injection From To
  injection = record { to = to; injective = injective }

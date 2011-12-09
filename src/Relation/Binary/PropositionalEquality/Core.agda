------------------------------------------------------------------------
-- The Agda standard library
--
-- Propositional equality
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Relation.Binary.PropositionalEquality.

module Relation.Binary.PropositionalEquality.Core where

open import Level
open import Relation.Binary.Core
open import Relation.Binary.Consequences.Core

------------------------------------------------------------------------
-- Some properties

sym : ∀ {a} {A : Set a} → Symmetric (_≡_ {A = A})
sym refl = refl

trans : ∀ {a} {A : Set a} → Transitive (_≡_ {A = A})
trans refl eq = eq

subst : ∀ {a p} {A : Set a} → Substitutive (_≡_ {A = A}) p
subst P refl p = p

resp₂ : ∀ {a ℓ} {A : Set a} (∼ : Rel A ℓ) → ∼ Respects₂ _≡_
resp₂ _∼_ = subst⟶resp₂ _∼_ subst

isEquivalence : ∀ {a} {A : Set a} → IsEquivalence (_≡_ {A = A})
isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed binary relations
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Relation.Binary.Indexed.

module Relation.Binary.Indexed.Core where

open import Function
open import Level
import Relation.Binary.Core as B
import Relation.Binary.Core as P

------------------------------------------------------------------------
-- Indexed binary relations

-- Heterogeneous.

REL : ∀ {i₁ i₂ a₁ a₂} {I₁ : Set i₁} {I₂ : Set i₂} →
      (I₁ → Set a₁) → (I₂ → Set a₂) → (ℓ : Level) → Set _
REL A₁ A₂ ℓ = ∀ {i₁ i₂} → A₁ i₁ → A₂ i₂ → Set ℓ

-- Homogeneous.

Rel : ∀ {i a} {I : Set i} → (I → Set a) → (ℓ : Level) → Set _
Rel A ℓ = REL A A ℓ

------------------------------------------------------------------------
-- Simple properties of indexed binary relations

-- Reflexivity.

Reflexive : ∀ {i a ℓ} {I : Set i} (A : I → Set a) → Rel A ℓ → Set _
Reflexive _ _∼_ = ∀ {i} → B.Reflexive (_∼_ {i})

-- Symmetry.

Symmetric : ∀ {i a ℓ} {I : Set i} (A : I → Set a) → Rel A ℓ → Set _
Symmetric _ _∼_ = ∀ {i j} → B.Sym (_∼_ {i} {j}) _∼_

-- Transitivity.

Transitive : ∀ {i a ℓ} {I : Set i} (A : I → Set a) → Rel A ℓ → Set _
Transitive _ _∼_ = ∀ {i j k} → B.Trans _∼_ (_∼_ {j}) (_∼_ {i} {k})

------------------------------------------------------------------------
-- Setoids

record IsEquivalence {i a ℓ} {I : Set i} (A : I → Set a)
                     (_≈_ : Rel A ℓ) : Set (i ⊔ a ⊔ ℓ) where
  field
    refl  : Reflexive A _≈_
    sym   : Symmetric A _≈_
    trans : Transitive A _≈_

  reflexive : ∀ {i} → P._≡_ ⟨ B._⇒_ ⟩ _≈_ {i}
  reflexive P.refl = refl

record Setoid {i} (I : Set i) c ℓ : Set (suc (i ⊔ c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : I → Set c
    _≈_           : Rel Carrier ℓ
    isEquivalence : IsEquivalence Carrier _≈_

  open IsEquivalence isEquivalence public

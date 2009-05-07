------------------------------------------------------------------------
-- Morphisms between algebraic structures
------------------------------------------------------------------------

module Algebra.Morphism where

open import Relation.Binary
open import Algebra
open import Algebra.FunctionProperties
open import Data.Function

------------------------------------------------------------------------
-- Basic definitions

module Definitions (From To : Set) (_≈_ : Rel To) where
  Morphism : Set
  Morphism = From → To

  Homomorphic₀ : Morphism → From → To → Set
  Homomorphic₀ ⟦_⟧ ∙ ∘ = ⟦ ∙ ⟧ ≈ ∘

  Homomorphic₁ : Morphism → Fun₁ From → Op₁ To → Set
  Homomorphic₁ ⟦_⟧ ∙_ ∘_ = ∀ x → ⟦ ∙ x ⟧ ≈ ∘ ⟦ x ⟧

  Homomorphic₂ : Morphism → Fun₂ From → Op₂ To → Set
  Homomorphic₂ ⟦_⟧ _∙_ _∘_ =
    ∀ x y → ⟦ x ∙ y ⟧ ≈ (⟦ x ⟧ ∘ ⟦ y ⟧)

------------------------------------------------------------------------
-- Some specific morphisms

-- Other morphisms could of course be defined.

record _-RawRing⟶_ (From To : RawRing) : Set where
  open RawRing
  open Definitions (carrier From) (carrier To) (_≈_ To)
  field
    ⟦_⟧    : Morphism
    +-homo : Homomorphic₂ ⟦_⟧ (_+_ From) (_+_ To)
    *-homo : Homomorphic₂ ⟦_⟧ (_*_ From) (_*_ To)
    -‿homo : Homomorphic₁ ⟦_⟧ (-_  From) (-_  To)
    0-homo : Homomorphic₀ ⟦_⟧ (0#  From) (0#  To)
    1-homo : Homomorphic₀ ⟦_⟧ (1#  From) (1#  To)

_-Ring⟶_ : Ring → Ring → Set
From -Ring⟶ To = rawRing From -RawRing⟶ rawRing To
  where open Ring

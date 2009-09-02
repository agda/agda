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
-- An example showing how a morphism type can be defined

record _-Ring⟶_ (From To : Ring) : Set where
  open Ring
  open Definitions (carrier From) (carrier To) (_≈_ To)
  field
    ⟦_⟧       : Morphism
    ⟦⟧-pres-≈ : ⟦_⟧ Preserves (_≈_ From) ⟶ (_≈_ To)
    +-homo    : Homomorphic₂ ⟦_⟧ (_+_ From) (_+_ To)
    *-homo    : Homomorphic₂ ⟦_⟧ (_*_ From) (_*_ To)
    -‿homo    : Homomorphic₁ ⟦_⟧ (-_  From) (-_  To)
    0-homo    : Homomorphic₀ ⟦_⟧ (0#  From) (0#  To)
    1-homo    : Homomorphic₀ ⟦_⟧ (1#  From) (1#  To)

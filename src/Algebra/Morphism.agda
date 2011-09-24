------------------------------------------------------------------------
-- The Agda standard library
--
-- Morphisms between algebraic structures
------------------------------------------------------------------------

module Algebra.Morphism where

open import Relation.Binary
open import Algebra
open import Algebra.FunctionProperties
import Algebra.Props.Group as GroupP
open import Function
open import Data.Product
open import Level
import Relation.Binary.EqReasoning as EqR

------------------------------------------------------------------------
-- Basic definitions

module Definitions {f t ℓ}
                   (From : Set f) (To : Set t) (_≈_ : Rel To ℓ) where
  Morphism : Set _
  Morphism = From → To

  Homomorphic₀ : Morphism → From → To → Set _
  Homomorphic₀ ⟦_⟧ ∙ ∘ = ⟦ ∙ ⟧ ≈ ∘

  Homomorphic₁ : Morphism → Fun₁ From → Op₁ To → Set _
  Homomorphic₁ ⟦_⟧ ∙_ ∘_ = ∀ x → ⟦ ∙ x ⟧ ≈ ∘ ⟦ x ⟧

  Homomorphic₂ : Morphism → Fun₂ From → Op₂ To → Set _
  Homomorphic₂ ⟦_⟧ _∙_ _∘_ =
    ∀ x y → ⟦ x ∙ y ⟧ ≈ (⟦ x ⟧ ∘ ⟦ y ⟧)

------------------------------------------------------------------------
-- An example showing how a morphism type can be defined

-- Ring homomorphisms.

record _-Ring⟶_ {r₁ r₂ r₃ r₄}
                (From : Ring r₁ r₂) (To : Ring r₃ r₄) :
                Set (r₁ ⊔ r₂ ⊔ r₃ ⊔ r₄) where
  private
    module F = Ring From
    module T = Ring To
  open Definitions F.Carrier T.Carrier T._≈_

  field
    ⟦_⟧     : Morphism
    ⟦⟧-cong : ⟦_⟧ Preserves F._≈_ ⟶ T._≈_
    +-homo  : Homomorphic₂ ⟦_⟧ F._+_ T._+_
    *-homo  : Homomorphic₂ ⟦_⟧ F._*_ T._*_
    1-homo  : Homomorphic₀ ⟦_⟧ F.1#  T.1#

  open EqR T.setoid

  0-homo : Homomorphic₀ ⟦_⟧ F.0# T.0#
  0-homo =
    GroupP.left-identity-unique T.+-group ⟦ F.0# ⟧ ⟦ F.0# ⟧ (begin
      T._+_ ⟦ F.0# ⟧ ⟦ F.0# ⟧ ≈⟨ T.sym (+-homo F.0# F.0#) ⟩
      ⟦ F._+_ F.0# F.0# ⟧     ≈⟨ ⟦⟧-cong (proj₁ F.+-identity F.0#) ⟩
      ⟦ F.0# ⟧                ∎)

  -‿homo : Homomorphic₁ ⟦_⟧ F.-_ T.-_
  -‿homo x =
    GroupP.left-inverse-unique T.+-group ⟦ F.-_ x ⟧ ⟦ x ⟧ (begin
      T._+_ ⟦ F.-_ x ⟧ ⟦ x ⟧ ≈⟨ T.sym (+-homo (F.-_ x) x) ⟩
      ⟦ F._+_ (F.-_ x) x ⟧   ≈⟨ ⟦⟧-cong (proj₁ F.-‿inverse x) ⟩
      ⟦ F.0# ⟧               ≈⟨ 0-homo ⟩
      T.0#                   ∎)

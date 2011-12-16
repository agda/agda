------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra

module Algebra.Props.AbelianGroup
         {g₁ g₂} (G : AbelianGroup g₁ g₂) where

import Algebra.Props.Group as GP
open import Data.Product
open import Function
import Relation.Binary.EqReasoning as EqR

open AbelianGroup G
open EqR setoid

open GP group public

private
  lemma : ∀ x y → x ∙ y ∙ x ⁻¹ ≈ y
  lemma x y = begin
    x ∙ y ∙ x ⁻¹    ≈⟨ comm _ _ ⟨ ∙-cong ⟩ refl ⟩
    y ∙ x ∙ x ⁻¹    ≈⟨ assoc _ _ _ ⟩
    y ∙ (x ∙ x ⁻¹)  ≈⟨ refl ⟨ ∙-cong ⟩ proj₂ inverse _ ⟩
    y ∙ ε           ≈⟨ proj₂ identity _ ⟩
    y               ∎

⁻¹-∙-comm : ∀ x y → x ⁻¹ ∙ y ⁻¹ ≈ (x ∙ y) ⁻¹
⁻¹-∙-comm x y = begin
  x ⁻¹ ∙ y ⁻¹                         ≈⟨ comm _ _ ⟩
  y ⁻¹ ∙ x ⁻¹                         ≈⟨ sym $ lem ⟨ ∙-cong ⟩ refl ⟩
  x ∙ (y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹) ∙ x ⁻¹  ≈⟨ lemma _ _ ⟩
  y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹               ≈⟨ lemma _ _ ⟩
  (x ∙ y) ⁻¹                          ∎
  where
  lem = begin
    x ∙ (y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹)  ≈⟨ sym $ assoc _ _ _ ⟩
    x ∙ (y ∙ (x ∙ y) ⁻¹) ∙ y ⁻¹  ≈⟨ sym $ assoc _ _ _ ⟨ ∙-cong ⟩ refl ⟩
    x ∙ y ∙ (x ∙ y) ⁻¹ ∙ y ⁻¹    ≈⟨ proj₂ inverse _ ⟨ ∙-cong ⟩ refl ⟩
    ε ∙ y ⁻¹                     ≈⟨ proj₁ identity _ ⟩
    y ⁻¹                         ∎

------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Algebra

module Algebra.Props.AbelianGroup
         {g₁ g₂} (G : AbelianGroup g₁ g₂) where

open AbelianGroup G
import Relation.Binary.EqReasoning as EqR; open EqR setoid
open import Function
open import Data.Product

private
  lemma : ∀ x y → x ∙ y ∙ x ⁻¹ ≈ y
  lemma x y = begin
    x ∙ y ∙ x ⁻¹    ≈⟨ comm _ _ ⟨ ∙-cong ⟩ refl ⟩
    y ∙ x ∙ x ⁻¹    ≈⟨ assoc _ _ _ ⟩
    y ∙ (x ∙ x ⁻¹)  ≈⟨ refl ⟨ ∙-cong ⟩ proj₂ inverse _ ⟩
    y ∙ ε           ≈⟨ proj₂ identity _ ⟩
    y               ∎

-‿∙-comm : ∀ x y → x ⁻¹ ∙ y ⁻¹ ≈ (x ∙ y) ⁻¹
-‿∙-comm x y = begin
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

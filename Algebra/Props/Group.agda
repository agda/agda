------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra

module Algebra.Props.Group (g : Group) where

open Group g
import Relation.Binary.EqReasoning as EqR; open EqR setoid
open import Data.Function
open import Data.Product

⁻¹-involutive : ∀ x → x ⁻¹ ⁻¹ ≈ x
⁻¹-involutive x = begin
  x ⁻¹ ⁻¹               ≈⟨ sym $ proj₂ identity _ ⟩
  x ⁻¹ ⁻¹ ∙ ε           ≈⟨ byDef ⟨ ∙-pres-≈ ⟩ sym (proj₁ inverse _) ⟩
  x ⁻¹ ⁻¹ ∙ (x ⁻¹ ∙ x)  ≈⟨ sym $ assoc _ _ _ ⟩
  x ⁻¹ ⁻¹ ∙ x ⁻¹ ∙ x    ≈⟨ proj₁ inverse _ ⟨ ∙-pres-≈ ⟩ byDef ⟩
  ε ∙ x                 ≈⟨ proj₁ identity _ ⟩
  x                     ∎

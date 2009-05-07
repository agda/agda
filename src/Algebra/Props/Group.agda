------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra

module Algebra.Props.Group (g : Group) where

open Group g
import Algebra.FunctionProperties as P; open P _≈_
import Relation.Binary.EqReasoning as EqR; open EqR setoid
open import Data.Function
open import Data.Product

⁻¹-involutive : ∀ x → x ⁻¹ ⁻¹ ≈ x
⁻¹-involutive x = begin
  x ⁻¹ ⁻¹               ≈⟨ sym $ proj₂ identity _ ⟩
  x ⁻¹ ⁻¹ ∙ ε           ≈⟨ refl ⟨ ∙-pres-≈ ⟩ sym (proj₁ inverse _) ⟩
  x ⁻¹ ⁻¹ ∙ (x ⁻¹ ∙ x)  ≈⟨ sym $ assoc _ _ _ ⟩
  x ⁻¹ ⁻¹ ∙ x ⁻¹ ∙ x    ≈⟨ proj₁ inverse _ ⟨ ∙-pres-≈ ⟩ refl ⟩
  ε ∙ x                 ≈⟨ proj₁ identity _ ⟩
  x                     ∎

left-identity-unique : ∀ x y → x ∙ y ≈ y → x ≈ ε
left-identity-unique x y eq = begin
  x              ≈⟨ sym (proj₂ identity x) ⟩
  x ∙ ε          ≈⟨ refl ⟨ ∙-pres-≈ ⟩ sym (proj₂ inverse y) ⟩
  x ∙ (y ∙ y ⁻¹) ≈⟨ sym (assoc x y (y ⁻¹)) ⟩
  (x ∙ y) ∙ y ⁻¹ ≈⟨ eq ⟨ ∙-pres-≈ ⟩ refl ⟩
       y  ∙ y ⁻¹ ≈⟨ proj₂ inverse y ⟩
  ε              ∎

right-identity-unique : ∀ x y → x ∙ y ≈ x → y ≈ ε
right-identity-unique x y eq = begin
  y              ≈⟨ sym (proj₁ identity y) ⟩
  ε          ∙ y ≈⟨ sym (proj₁ inverse x) ⟨ ∙-pres-≈ ⟩ refl ⟩
  (x ⁻¹ ∙ x) ∙ y ≈⟨ assoc (x ⁻¹) x y ⟩
  x ⁻¹ ∙ (x ∙ y) ≈⟨ refl ⟨ ∙-pres-≈ ⟩ eq ⟩
  x ⁻¹ ∙  x      ≈⟨ proj₁ inverse x ⟩
  ε              ∎

identity-unique : ∀ {x} → Identity x _∙_ → x ≈ ε
identity-unique {x} id = left-identity-unique x x (proj₂ id x)

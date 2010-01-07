------------------------------------------------------------------------
-- Properties related to bag equality
------------------------------------------------------------------------

-- Bag equality is defined in Data.List.Any.

module Data.List.Any.BagEquality where

open import Data.List as List
open import Data.List.Any as Any
open import Data.List.Any.Properties as AnyProp
open import Data.Product
open import Function
open import Function.Inverse as Inv
  using (_⇿_) renaming (_∘_ to _⟪∘⟫_)
open import Relation.Binary
import Relation.Binary.HeterogeneousEquality as H
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≗_)
import Relation.Binary.Sigma.Pointwise as Σ
open import Relation.Binary.Sum

open Any.Membership-≡
open AnyProp.Membership-≡
private
  open module BagEq {A : Set} = Setoid (Bag-equality {A}) using (_≈_)

-- _++_ is a congruence.

_++-cong_ : {A : Set} {xs₁ xs₂ xs₃ xs₄ : List A} →
            xs₁ ≈ xs₂ → xs₃ ≈ xs₄ → xs₁ ++ xs₃ ≈ xs₂ ++ xs₄
xs₁≈xs₂ ++-cong xs₃≈xs₄ =
  ++⇿ ⟪∘⟫ ⊎-Rel⇿≡ ⟪∘⟫
  (xs₁≈xs₂ ⊎-inverse xs₃≈xs₄) ⟪∘⟫
  Inv.sym (++⇿ ⟪∘⟫ ⊎-Rel⇿≡)

-- List.map is a congruence.

map-cong : ∀ {A B : Set} {f₁ f₂ : A → B} {xs₁ xs₂} →
           f₁ ≗ f₂ → xs₁ ≈ xs₂ → List.map f₁ xs₁ ≈ List.map f₂ xs₂
map-cong {f₁ = f₁} {f₂} {xs₁} {xs₂} f₁≗f₂ xs₁≈xs₂ {fx} =
  map-∈⇿ ⟪∘⟫ Σ.Rel⇿≡ ⟪∘⟫
  Σ.inverse
    (H.≡⇿≅ (λ x → x ∈ xs₂ × fx ≡ f₂ x) ⟪∘⟫ ×-Rel⇿≡ ⟪∘⟫
     (xs₁≈xs₂ ×-inverse lemma) ⟪∘⟫
     Inv.sym (H.≡⇿≅ (λ x → x ∈ xs₁ × fx ≡ f₁ x) ⟪∘⟫ ×-Rel⇿≡)) ⟪∘⟫
  Inv.sym (map-∈⇿ ⟪∘⟫ Σ.Rel⇿≡)
  where
  lemma : ∀ {x y} → y ≡ f₁ x ⇿ y ≡ f₂ x
  lemma {x} = record
    { to         = P.→-to-⟶ (λ y≡f₁x → P.trans y≡f₁x (f₁≗f₂ x))
    ; from       = P.→-to-⟶ (λ y≡f₂x → P.trans y≡f₂x (P.sym $ f₁≗f₂ x))
    ; inverse-of = record
      { left-inverse-of  = λ _ → P.proof-irrelevance _ _
      ; right-inverse-of = λ _ → P.proof-irrelevance _ _
      }
    }

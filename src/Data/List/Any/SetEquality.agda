------------------------------------------------------------------------
-- Properties related to set equality
------------------------------------------------------------------------

-- Set equality is defined in Data.List.Any.

module Data.List.Any.SetEquality where

open import Data.List as List
open import Data.List.Any as Any
open import Data.List.Any.Properties
open import Data.List.Any.Membership as MembershipProp
open import Data.Product
open import Function
open import Function.Equivalence as Eq
  using (_⇔_) renaming (_∘_ to _⟨∘⟩_)
open import Function.Inverse
  using (module Inverse) renaming (_∘_ to _⟪∘⟫_)
open import Relation.Binary
import Relation.Binary.HeterogeneousEquality as H
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≗_)
import Relation.Binary.Sigma.Pointwise as Σ
open import Relation.Binary.Sum

open Any.Membership-≡
open MembershipProp.Membership-≡
private
  open module SetEq {A : Set} = Setoid (Set-equality {A}) using (_≈_)

-- _++_ is a congruence.

_++-cong_ : {A : Set} {xs₁ xs₂ xs₃ xs₄ : List A} →
            xs₁ ≈ xs₂ → xs₃ ≈ xs₄ → xs₁ ++ xs₃ ≈ xs₂ ++ xs₄
xs₁≈xs₂ ++-cong xs₃≈xs₄ =
  Inverse.equivalence (++⇿ ⟪∘⟫ ⊎-Rel⇿≡) ⟨∘⟩
  (xs₁≈xs₂ ⊎-equivalent xs₃≈xs₄) ⟨∘⟩
  Eq.sym (Inverse.equivalence $ ++⇿ ⟪∘⟫ ⊎-Rel⇿≡)

-- List.map is a congruence.

map-cong : ∀ {A B : Set} {f₁ f₂ : A → B} {xs₁ xs₂} →
           f₁ ≗ f₂ → xs₁ ≈ xs₂ → List.map f₁ xs₁ ≈ List.map f₂ xs₂
map-cong {f₁ = f₁} {f₂} {xs₁} {xs₂} f₁≗f₂ xs₁≈xs₂ {fx} =
  Inverse.equivalence (map-∈⇿ ⟪∘⟫ Σ.Rel⇿≡) ⟨∘⟩
  Σ.equivalent
    (Inverse.equivalence
       (H.≡⇿≅ (λ x → x ∈ xs₂ × fx ≡ f₂ x) ⟪∘⟫ ×-Rel⇿≡) ⟨∘⟩
     (xs₁≈xs₂ ×-equivalent lemma) ⟨∘⟩
     Eq.sym (Inverse.equivalence $
               H.≡⇿≅ (λ x → x ∈ xs₁ × fx ≡ f₁ x) ⟪∘⟫ ×-Rel⇿≡))
    ⟨∘⟩
  Eq.sym (Inverse.equivalence $ map-∈⇿ ⟪∘⟫ Σ.Rel⇿≡)
  where
  lemma : ∀ {x y} → y ≡ f₁ x ⇔ y ≡ f₂ x
  lemma {x} = record
    { to   = P.→-to-⟶ (λ y≡f₁x → P.trans y≡f₁x (f₁≗f₂ x))
    ; from = P.→-to-⟶ (λ y≡f₂x → P.trans y≡f₂x (P.sym $ f₁≗f₂ x))
    }

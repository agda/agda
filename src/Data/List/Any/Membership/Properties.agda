------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to propositional list membership
------------------------------------------------------------------------

open import Data.List
open import Data.List.Any as Any using (here; there)
open import Data.List.Any.Properties
import Data.List.Any.Membership as Membership
open import Data.Product using (∃; _×_; _,_)
open import Function using (flip)
open import Relation.Binary
open import Relation.Binary.InducedPreorders using (InducedPreorder₂)
open import Relation.Binary.List.Pointwise as ListEq
  using () renaming (Rel to ListRel)


module Data.List.Any.Membership.Properties where

module SingleSetoid {c ℓ} (S : Setoid c ℓ) where

  open Setoid S
  open import Data.List.Any.Membership S

  -- Equality is respected by the predicate which is used to define
  -- _∈_.

  ∈-resp-≈ : ∀ {x} → (x ≈_) Respects _≈_
  ∈-resp-≈ = flip trans

  -- List equality is respected by _∈_.

  ∈-resp-≋ : ∀ {x} → (x ∈_) Respects (ListRel _≈_)
  ∈-resp-≋ = lift-resp ∈-resp-≈

  -- _⊆_ is a preorder.

  ⊆-preorder : Preorder _ _ _
  ⊆-preorder = InducedPreorder₂ (ListEq.setoid S) _∈_ ∈-resp-≋

  module ⊆-Reasoning where
    import Relation.Binary.PreorderReasoning as PreR
    open PreR ⊆-preorder public
      renaming (_∼⟨_⟩_ to _⊆⟨_⟩_)

    infix 1 _∈⟨_⟩_

    _∈⟨_⟩_ : ∀ x {xs ys} → x ∈ xs → xs IsRelatedTo ys → x ∈ ys
    x ∈⟨ x∈xs ⟩ xs⊆ys = (begin xs⊆ys) x∈xs

open SingleSetoid public


module DoubleSetoid {c₁ c₂ ℓ₁ ℓ₂}
  (S₁ : Setoid c₁ ℓ₁) (S₂ : Setoid c₂ ℓ₂) where

  open Setoid S₁ renaming (Carrier to A₁; _≈_ to _≈₁_; refl to refl₁)
  open Setoid S₂ renaming (Carrier to A₂; _≈_ to _≈₂_)

  open Membership S₁ using (find) renaming (_∈_ to _∈₁_)
  open Membership S₂ using () renaming (_∈_ to _∈₂_)

  ∈-map⁺ : ∀ {f} → f Preserves _≈₁_ ⟶ _≈₂_ → ∀ {x xs} →
            x ∈₁ xs → f x ∈₂ map f xs
  ∈-map⁺ pres x∈xs = map⁺ (Any.map pres x∈xs)

  ∈-map⁻ : ∀ {y xs f} → y ∈₂ map f xs →
           ∃ λ x → x ∈₁ xs × y ≈₂ f x
  ∈-map⁻ x∈map = find (map⁻ x∈map)

open DoubleSetoid public

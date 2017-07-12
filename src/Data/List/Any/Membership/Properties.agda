------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to propositional list membership
------------------------------------------------------------------------

open import Data.List.Any.Properties using (lift-resp)
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

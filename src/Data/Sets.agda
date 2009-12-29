------------------------------------------------------------------------
-- Finite sets (currently only some type signatures)
------------------------------------------------------------------------

module Data.Sets where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.OrderMorphism
open import Function
open import Data.List as L using (List)
open import Data.Product using (∃; _×_)
open import Level

module Sets₁ (dto : DecTotalOrder zero zero zero) where

  open DecTotalOrder dto public using (_≈_)
  open DecTotalOrder dto hiding (_≈_)

  infixr 6 _∪_
  infix  5 _∈?_
  infix  4 _∈_ _|≈|_

  abstract postulate decSetoid : DecSetoid _ _

  <Set> : Set
  <Set> = DecSetoid.Carrier decSetoid

  _|≈|_ : Rel <Set> zero
  _|≈|_ = DecSetoid._≈_ decSetoid

  abstract
   postulate
    empty  : <Set>
    insert : Carrier → <Set> → <Set>
    _∪_    : <Set> → <Set> → <Set>
    _∈_    : Carrier → <Set> → Set
    _∈?_   : (x : Carrier) → (s : <Set>) → Dec (x ∈ s)
    toList : <Set> → List Carrier

   postulate
    prop-∈-insert₁ : ∀ {x y s} → x ≈ y → x ∈ insert y s
    prop-∈-insert₂ : ∀ {x y s} → x ∈ s → x ∈ insert y s
    prop-∈-insert₃ : ∀ {x y s} → ¬ x ≈ y → x ∈ insert y s → x ∈ s

    prop-∈-empty : ∀ {x} → ¬ x ∈ empty

    prop-∈-∪ : ∀ {x s₁ s₂} → x ∈ s₁ → x ∈ s₁ ∪ s₂

    prop-∪₁ : ∀ {s₁ s₂}    → s₁ ∪ s₂        |≈| s₂ ∪ s₁
    prop-∪₂ : ∀ {s₁ s₂ s₃} → s₁ ∪ (s₂ ∪ s₃) |≈| (s₁ ∪ s₂) ∪ s₃

    prop-∈-|≈| : ∀ {x} → (λ s → x ∈ s) Respects _|≈|_
    prop-∈-≈   : ∀ {s} → (λ x → x ∈ s) Respects  _≈_

    -- TODO: Postulates for toList.

  singleton : Carrier → <Set>
  singleton x = insert x empty

  ⋃_ : List <Set> → <Set>
  ⋃_ = L.foldr _∪_ empty

  fromList : List Carrier → <Set>
  fromList = L.foldr insert empty

  _⊆_ : <Set> → <Set> → Set
  s₁ ⊆ s₂ = ∀ x → x ∈ s₁ → x ∈ s₂

open Sets₁ public
open DecTotalOrder hiding (_≈_)
open _⇒-Poset_

abstract
 postulate
  map : ∀ {do₁ do₂} → do₁ ⇒-DTO do₂ → <Set> do₁ → <Set> do₂
  mapToSet : ∀ {do₁ do₂} →
             (Carrier do₁ → <Set> do₂) →
             <Set> do₁ → <Set> do₂

  prop-map-∈₁ : ∀ {do₁ do₂ f x s} →
                      x ⟨ _∈_ do₁ ⟩       s →
                fun f x ⟨ _∈_ do₂ ⟩ map f s
  prop-map-∈₂ : ∀ {do₁ do₂ f y s} →
                y ⟨ _∈_ do₂ ⟩ map f s →
                ∃ λ x → (fun f x ⟨ _≈_ do₂ ⟩ y) ×
                        (      x ⟨ _∈_ do₁ ⟩ s)

  prop-mapToSet₁ : ∀ {do₁ do₂ f x s} →
                     x ⟨ _∈_ do₁ ⟩            s →
                   f x ⟨ _⊆_ do₂ ⟩ mapToSet f s
  prop-mapToSet₂ : ∀ {do₁ do₂ f y s} →
                   y ⟨ _∈_ do₂ ⟩ mapToSet f s →
                   ∃ λ x → (y ⟨ _∈_ do₂ ⟩ f x) ×
                           (x ⟨ _∈_ do₁ ⟩ s)

------------------------------------------------------------------------
-- Finite sets (currently only some type signatures)
------------------------------------------------------------------------

module Data.Sets where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.OrderMorphism
open import Data.Function
open import Data.List as L using (List)
open import Data.Product using (∃; _×_)

module Sets₁ (dto : DecTotalOrder) where

  open DecTotalOrder dto public using (_≈_)
  open DecTotalOrder dto hiding (_≈_)

  infixr 6 _∪_
  infix  5 _∈?_
  infix  4 _∈_ _|≈|_

  abstract postulate decSetoid : DecSetoid

  <Set> : Set
  <Set> = DecSetoid.carrier decSetoid

  _|≈|_ : Rel <Set>
  _|≈|_ = DecSetoid._≈_ decSetoid

  abstract
   postulate
    empty  : <Set>
    insert : carrier → <Set> → <Set>
    _∪_    : <Set> → <Set> → <Set>
    _∈_    : carrier → <Set> → Set
    _∈?_   : (x : carrier) → (s : <Set>) → Dec (x ∈ s)
    toList : <Set> → List carrier

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

  singleton : carrier → <Set>
  singleton x = insert x empty

  ⋃_ : List <Set> → <Set>
  ⋃_ = L.foldr _∪_ empty

  fromList : List carrier → <Set>
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
             (carrier do₁ → <Set> do₂) →
             <Set> do₁ → <Set> do₂

  prop-map-∈₁ : ∀ {do₁ do₂ f x s} →
                      x ⟨ _∈_ do₁ ⟩₁       s →
                fun f x ⟨ _∈_ do₂ ⟩₁ map f s
  prop-map-∈₂ : ∀ {do₁ do₂ f y s} →
                y ⟨ _∈_ do₂ ⟩₁ map f s →
                ∃ λ x → (fun f x ⟨ _≈_ do₂ ⟩₁ y) ×
                        (      x ⟨ _∈_ do₁ ⟩₁ s)

  prop-mapToSet₁ : ∀ {do₁ do₂ f x s} →
                     x ⟨ _∈_ do₁ ⟩₁            s →
                   f x ⟨ _⊆_ do₂ ⟩₁ mapToSet f s
  prop-mapToSet₂ : ∀ {do₁ do₂ f y s} →
                   y ⟨ _∈_ do₂ ⟩₁ mapToSet f s →
                   ∃ λ x → (y ⟨ _∈_ do₂ ⟩₁ f x) ×
                           (x ⟨ _∈_ do₁ ⟩₁ s)

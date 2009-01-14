------------------------------------------------------------------------
-- Finite maps, i.e. lookup tables (currently only some type
-- signatures)
------------------------------------------------------------------------

module Data.Map where

open import Relation.Nullary
open import Relation.Binary
import Data.List as L
open L using (List)
open import Data.Product

module Map₁ (key-dto : DecTotalOrder) (elem-s : Setoid) where

  open DecTotalOrder key-dto renaming (carrier to key)
  open Setoid elem-s         renaming (carrier to elem; _≈_ to _≗_)

  infixr 6 _∪_
  infix  5 _∈?_
  infix  4 _∈_ _|≈|_

  abstract postulate decSetoid : DecSetoid

  Map : Set
  Map = Setoid.carrier (DecSetoid.setoid decSetoid)

  _|≈|_ : Rel Map
  _|≈|_ = Setoid._≈_ (DecSetoid.setoid decSetoid)

  abstract
   postulate
    empty  : Map
    insert : key → elem → Map → Map
    _∪_    : Map → Map → Map
    _∈_    : key → Map → Set
    _↦_∈_  : key → elem → Map → Set

  data LookupResult (k : key) (s : Map) : Set where
    found    : (e : elem) (k↦e∈s : k ↦ e ∈ s) → LookupResult k s
    notFound : (k∉s : ¬ k ∈ s) → LookupResult k s

  abstract
   postulate
    _∈?_   : (k : key) → (s : Map) → LookupResult k s
    toList : Map → List (key × elem)

   postulate
    prop-∈₁ : ∀ {x v s}   → x ↦ v ∈ s → x ∈ s
    prop-∈₂ : ∀ {x s}     → x ∈ s → Σ elem (λ v → x ↦ v ∈ s)
    prop-∈₃ : ∀ {x v w s} → x ↦ v ∈ s → x ↦ w ∈ s → v ≗ w

    prop-∈-insert₁ : ∀ {x y v w s} →
                     x ≈ y → v ≗ w → x ↦ v ∈ insert y w s
    prop-∈-insert₂ : ∀ {x y v w s} →
                     ¬ x ≈ y → x ↦ v ∈ s → x ↦ v ∈ insert y w s
    prop-∈-insert₃ : ∀ {x y v w s} →
                     ¬ x ≈ y → x ↦ v ∈ insert y w s → x ↦ v ∈ s

    prop-∈-empty : ∀ {x} → ¬ x ∈ empty

    prop-∈-∪ : ∀ {x s₁ s₂} → x ∈ s₁ → x ∈ s₁ ∪ s₂

    prop-∪₁ : ∀ {s₁ s₂}    → s₁ ∪ s₂        |≈| s₂ ∪ s₁
    prop-∪₂ : ∀ {s₁ s₂ s₃} → s₁ ∪ (s₂ ∪ s₃) |≈| (s₁ ∪ s₂) ∪ s₃

    prop-∈-|≈|₁ : ∀ {x}   → _|≈|_ Respects (λ s → x ∈ s)
    prop-∈-|≈|₂ : ∀ {x v} → _|≈|_ Respects (λ s → x ↦ v ∈ s)
    prop-∈-≈₁   : ∀ {s}   → _≈_   Respects (λ x → x ∈ s)
    prop-∈-≈₂   : ∀ {v s} → _≈_   Respects (λ x → x ↦ v ∈ s)
    prop-∈-≗    : ∀ {x s} → _≗_   Respects (λ v → x ↦ v ∈ s)

    -- TODO: Postulates for toList.

  singleton : key → elem → Map
  singleton k v = insert k v empty

  ⋃_ : List Map → Map
  ⋃_ = L.foldr _∪_ empty

  fromList : List (key × elem) → Map
  fromList = L.foldr (uncurry insert) empty

open Map₁ public renaming (Map to _⇰_)

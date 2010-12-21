------------------------------------------------------------------------
-- Subsets of finite sets
------------------------------------------------------------------------

module Data.Fin.Subset where

open import Data.Nat hiding (_≟_)
open import Data.Bool
open import Data.Vec hiding (_∈_)
import Data.List as List
open import Data.Fin
open import Data.Product
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

infixr 2 _∈_ _∉_ _⊆_ _⊈_

------------------------------------------------------------------------
-- Definitions

-- Partitions a finite set into two parts, the inside and the outside.

Side : Set
Side = Bool

inside : Side
inside = true

outside : Side
outside = false

Subset : ℕ → Set
Subset = Vec Bool

------------------------------------------------------------------------
-- Membership and subset predicates

_∈_ : ∀ {n} → Fin n → Subset n → Set
x ∈ p = p [ x ]= true

_∉_ : ∀ {n} → Fin n → Subset n → Set
x ∉ p = ¬ (x ∈ p)

_⊆_ : ∀ {n} → Subset n → Subset n → Set
p₁ ⊆ p₂ = ∀ {x} → x ∈ p₁ → x ∈ p₂

_⊈_ : ∀ {n} → Subset n → Subset n → Set
p₁ ⊈ p₂ = ¬ (p₁ ⊆ p₂)

------------------------------------------------------------------------
-- Some specific subsets

all : ∀ {n} → Bool → Subset n
all {zero}  _ = []
all {suc n} s = s ∷ all s

------------------------------------------------------------------------
-- Set operations

_∪_ : ∀ {n} → Subset n → Subset n → Subset n
[] ∪ xs = xs
(x ∷ xs) ∪ (y ∷ ys) = (x ∨ y) ∷ xs ∪ ys

_∩_ : ∀ {n} → Subset n → Subset n → Subset n
[] ∩ _ = []
(x ∷ xs) ∩ (y ∷ ys) = x ∧ y ∷ xs ∩ ys

∅ : ∀ {n} → Subset n
∅ {suc n} = false ∷ ∅ {n}
∅ {zero}  = []

full  : ∀ {n} → Subset n
full = all true

⁅_⁆ : ∀ {n} → Fin n → Subset n
⁅ zero ⁆ = true ∷ ∅
⁅ suc i ⁆ = false ∷ ⁅ i ⁆

⋃ : ∀ {n} → List.List (Subset n) → Subset n
⋃ = List.foldr _∪_ ∅

------------------------------------------------------------------------
-- Properties

Nonempty : ∀ {n} (p : Subset n) → Set
Nonempty p = ∃ λ f → f ∈ p

Empty : ∀ {n} (p : Subset n) → Set
Empty p = ¬ Nonempty p

-- Point-wise lifting of properties.

Lift : ∀ {n} → (Fin n → Set) → (Subset n → Set)
Lift P p = ∀ {x} → x ∈ p → P x
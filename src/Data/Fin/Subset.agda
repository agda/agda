------------------------------------------------------------------------
-- The Agda standard library
--
-- Subsets of finite sets
------------------------------------------------------------------------

module Data.Fin.Subset where

open import Algebra
import Algebra.Properties.BooleanAlgebra as BoolAlgProp
import Algebra.Properties.BooleanAlgebra.Expression as BAExpr
open import Data.Bool.Properties using (∨-∧-booleanAlgebra)
open import Data.Fin
open import Data.List.Base using (List; foldr; foldl)
open import Data.Nat
open import Data.Product
open import Data.Vec using (Vec; _∷_; _[_]=_)
import Data.Vec.Relation.Pointwise as Pointwise
open import Relation.Nullary

------------------------------------------------------------------------
-- Definitions

-- Sides.

open import Data.Bool.Base public
  using () renaming (Bool to Side; true to inside; false to outside)

-- Partitions a finite set into two parts, the inside and the outside.

Subset : ℕ → Set
Subset = Vec Side

------------------------------------------------------------------------
-- Membership and subset predicates

infix 4 _∈_ _∉_ _⊆_ _⊈_

_∈_ : ∀ {n} → Fin n → Subset n → Set
x ∈ p = p [ x ]= inside

_∉_ : ∀ {n} → Fin n → Subset n → Set
x ∉ p = ¬ (x ∈ p)

_⊆_ : ∀ {n} → Subset n → Subset n → Set
p₁ ⊆ p₂ = ∀ {x} → x ∈ p₁ → x ∈ p₂

_⊈_ : ∀ {n} → Subset n → Subset n → Set
p₁ ⊈ p₂ = ¬ (p₁ ⊆ p₂)

------------------------------------------------------------------------
-- Set operations

-- Pointwise lifting of the usual boolean algebra for booleans gives
-- us a boolean algebra for subsets.
--
-- The underlying equality of the returned boolean algebra is
-- propositional equality.

booleanAlgebra : ℕ → BooleanAlgebra _ _
booleanAlgebra n =
  BoolAlgProp.replace-equality
    (BAExpr.lift ∨-∧-booleanAlgebra n)
    Pointwise.Pointwise-≡

private
  open module BA {n} = BooleanAlgebra (booleanAlgebra n) public
    using
      ( ⊥  -- The empty subset.
      ; ⊤  -- The subset containing all elements.
      )
    renaming
      ( _∨_ to _∪_  -- Binary union.
      ; _∧_ to _∩_  -- Binary intersection.
      ; ¬_  to ∁    -- Complement.
      )

-- A singleton subset, containing just the given element.

⁅_⁆ : ∀ {n} → Fin n → Subset n
⁅ zero  ⁆ = inside  ∷ ⊥
⁅ suc i ⁆ = outside ∷ ⁅ i ⁆

-- N-ary union.

⋃ : ∀ {n} → List (Subset n) → Subset n
⋃ = foldr _∪_ ⊥

-- N-ary intersection.

⋂ : ∀ {n} → List (Subset n) → Subset n
⋂ = foldr _∩_ ⊤

------------------------------------------------------------------------
-- Properties

Nonempty : ∀ {n} (p : Subset n) → Set
Nonempty p = ∃ λ f → f ∈ p

Empty : ∀ {n} (p : Subset n) → Set
Empty p = ¬ Nonempty p

-- Point-wise lifting of properties.

Lift : ∀ {n} → (Fin n → Set) → (Subset n → Set)
Lift P p = ∀ {x} → x ∈ p → P x

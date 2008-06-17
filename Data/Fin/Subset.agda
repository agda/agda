------------------------------------------------------------------------
-- Subsets of finite sets
------------------------------------------------------------------------

module Data.Fin.Subset where

open import Data.Nat
open import Data.Vec hiding (_∈_)
open import Data.Fin
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

infixr 2 _∈_ _∉_ _⊆_ _⊈_

------------------------------------------------------------------------
-- Definitions

data Side : Set where
  inside  : Side
  outside : Side

-- Partitions a finite set into two parts, the inside and the outside.

Subset : ℕ -> Set
Subset = Vec Side

------------------------------------------------------------------------
-- Membership and subset predicates

_∈_ : forall {n} -> Fin n -> Subset n -> Set
x ∈ p = p [ x ]= inside

_∉_ : forall {n} -> Fin n -> Subset n -> Set
x ∉ p = ¬ (x ∈ p)

_⊆_ : forall {n} -> Subset n -> Subset n -> Set
p₁ ⊆ p₂ = forall {x} -> x ∈ p₁ -> x ∈ p₂

_⊈_ : forall {n} -> Subset n -> Subset n -> Set
p₁ ⊈ p₂ = ¬ (p₁ ⊆ p₂)

------------------------------------------------------------------------
-- Some specific subsets

all : forall {n} -> Side -> Subset n
all {zero}  _ = []
all {suc n} s = s ∷ all s

------------------------------------------------------------------------
-- Properties

Nonempty : forall {n} (p : Subset n) -> Set
Nonempty p = ∃ \f -> f ∈ p

Empty : forall {n} (p : Subset n) -> Set
Empty p = ¬ Nonempty p

-- Point-wise lifting of properties.

Lift : forall {n} -> (Fin n -> Set) -> (Subset n -> Set)
Lift P p = forall {x} -> x ∈ p -> P x

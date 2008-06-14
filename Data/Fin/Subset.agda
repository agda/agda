------------------------------------------------------------------------
-- Subsets of finite sets
------------------------------------------------------------------------

module Data.Fin.Subset where

open import Data.Nat
open import Data.Fin
open import Data.Product
open import Relation.Nullary

infixl 5 _▻_
infixr 2 _∈_ _∉_ _⊆_ _⊈_

------------------------------------------------------------------------
-- Definitions

data Side : Set where
  inside  : Side
  outside : Side

-- Partitions a finite set into two parts, the inside and the outside.

data Subset : ℕ -> Set where
  ε   : Subset zero
  _▻_ : forall {n} -> Subset n -> Side -> Subset (suc n)

------------------------------------------------------------------------
-- Membership and subset predicates

data _∈_ : forall {n} -> Fin n -> Subset n -> Set where
  zeroIn : forall {n}     {p : Subset n} -> zero ∈ p ▻ inside
  sucIn  : forall {s n x} {p : Subset n} -> x ∈ p -> suc x ∈ p ▻ s

_∉_ : forall {n} -> Fin n -> Subset n -> Set
x ∉ p = ¬ (x ∈ p)

_⊆_ : forall {n} -> Subset n -> Subset n -> Set
p₁ ⊆ p₂ = forall {x} -> x ∈ p₁ -> x ∈ p₂

_⊈_ : forall {n} -> Subset n -> Subset n -> Set
p₁ ⊈ p₂ = ¬ (p₁ ⊆ p₂)

------------------------------------------------------------------------
-- Some specific subsets

all : forall {n} -> Side -> Subset n
all {zero}  _ = ε
all {suc n} s = all s ▻ s

------------------------------------------------------------------------
-- Properties

Nonempty : forall {n} (p : Subset n) -> Set
Nonempty p = ∃ \f -> f ∈ p

Empty : forall {n} (p : Subset n) -> Set
Empty p = ¬ Nonempty p

-- Point-wise lifting of properties.

Lift : forall {n} -> (Fin n -> Set) -> (Subset n -> Set)
Lift P p = forall {x} -> x ∈ p -> P x

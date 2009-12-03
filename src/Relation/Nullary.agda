------------------------------------------------------------------------
-- Operations on nullary relations (like negation and decidability)
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

-- Some operations on/properties of nullary relations, i.e. sets.

module Relation.Nullary where

open import Data.Product
open import Level
import Relation.Nullary.Core as Core

------------------------------------------------------------------------
-- Negation

open Core public using (¬_)

------------------------------------------------------------------------
-- Equivalence

infix 3 _⇔_

_⇔_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
P ⇔ Q = (P → Q) × (Q → P)

------------------------------------------------------------------------
-- Decidable relations

open Core public using (Dec; yes; no)

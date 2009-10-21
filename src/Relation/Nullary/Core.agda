------------------------------------------------------------------------
-- Nullary relations (some core definitions)
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

-- The definitions in this file are reexported by Relation.Nullary.

module Relation.Nullary.Core where

open import Data.Empty
open import Level

-- Negation.

infix 3 ¬_

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⊥

-- Decidable relations.

data Dec (P : Set) : Set where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

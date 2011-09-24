------------------------------------------------------------------------
-- The Agda standard library
--
-- Nullary relations (some core definitions)
------------------------------------------------------------------------

-- The definitions in this file are reexported by Relation.Nullary.

module Relation.Nullary.Core where

open import Data.Empty
open import Level

-- Negation.

infix 3 ¬_

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⊥

-- Decidable relations.

data Dec {p} (P : Set p) : Set p where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on nullary relations (like negation and decidability)
------------------------------------------------------------------------

-- Some operations on/properties of nullary relations, i.e. sets.

module Relation.Nullary where

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

------------------------------------------------------------------------
-- Nullary relations (some core definitions)
------------------------------------------------------------------------

-- The definitions in this file are reexported by Relation.Nullary.

module Relation.Nullary.Core where

open import Data.Empty

-- Negation.

infix 3 ¬_

¬_ : Set → Set
¬ P = P → ⊥

-- Decidable relations.

data Dec (P : Set) : Set where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

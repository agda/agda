------------------------------------------------------------------------
-- Some basic logic-related stuff
------------------------------------------------------------------------

module Prelude.Logic where

infix 4 _≡_ _≡₁_
infix  3 ¬_

-- Propositional equality.

data _≡_ {a : Set} (x : a) : a -> Set where
  ≡-refl : x ≡ x

data _≡₁_ {a : Set1} (x : a) : a -> Set where
  ≡₁-refl : x ≡₁ x

-- Empty type.

data ⊥ : Set where

⊥-elim : {whatever : Set} -> ⊥ -> whatever
⊥-elim ()

-- Negation.

¬_ : Set -> Set
¬ P = P -> ⊥

-- Existential.

record ∃ (a : Set) (P : a -> Set) : Set where
  witness : a
  proof   : P witness

-- Decidable property.

data Dec (P : Set) : Set where
  yes : P   -> Dec P
  no  : ¬ P -> Dec P

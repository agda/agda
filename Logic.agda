------------------------------------------------------------------------
-- Some basic logic-related stuff
------------------------------------------------------------------------

module Logic where

infix 4 _≡_ _≡₁_ _≢_ _≢₁_
infix 3 ¬_

------------------------------------------------------------------------
-- Definitions

-- Propositional equality.

data _≡_ {a : Set} (x : a) : a -> Set where
  ≡-refl : x ≡ x

data _≡₁_ {a : Set1} (x : a) : a -> Set where
  ≡₁-refl : x ≡₁ x

-- Empty type.

data ⊥ : Set where

-- Negation.

¬_ : Set -> Set
¬ P = P -> ⊥

-- Nonequality.

_≢_ : {a : Set} -> a -> a -> Set
x ≢ y = ¬ (x ≡ y)

_≢₁_ : {a : Set1} -> a -> a -> Set
x ≢₁ y = ¬ (x ≡₁ y)

-- Existential.

record ∃ (a : Set) (P : a -> Set) : Set where
  witness : a
  proof   : P witness

------------------------------------------------------------------------
-- Some basic properties

⊥-elim : {whatever : Set} -> ⊥ -> whatever
⊥-elim ()

contradiction : forall {P whatever} -> P -> ¬ P -> whatever
contradiction p np = ⊥-elim (np p)

contravariant : forall {P Q} -> (P -> Q) -> ¬ Q -> ¬ P
contravariant f ¬q p = contradiction (f p) ¬q

map-¬¬ : forall {P Q} -> (P -> Q) -> ¬ (¬ P) -> ¬ (¬ Q)
map-¬¬ f = contravariant (contravariant f)

------------------------------------------------------------------------
-- Some basic logic-related stuff
------------------------------------------------------------------------

module Logic where

infix 4 _≡_ _≡₁_ _≢_ _≢₁_ _≅_ _≇_
infix 3 ¬_

------------------------------------------------------------------------
-- Definitions

-- Propositional equality.

data _≡_ {a : Set} (x : a) : a -> Set where
  ≡-refl : x ≡ x

data _≡₁_ {a : Set1} (x : a) : a -> Set where
  ≡₁-refl : x ≡₁ x

-- Heterogeneous equality.

data _≅_ {a : Set} (x : a) : {b : Set} -> b -> Set where
  ≅-refl : x ≅ x

-- Empty type.

data ⊥ : Set where

-- Negation.

¬_ : Set -> Set
¬ P = P -> ⊥

-- Nonequality.

_≢_ : {a : Set} -> a -> a -> Set
x ≢ y = ¬ x ≡ y

_≢₁_ : {a : Set1} -> a -> a -> Set
x ≢₁ y = ¬ x ≡₁ y

_≇_ : {a : Set} -> a -> {b : Set} -> b -> Set
x ≇ y = ¬ x ≅ y

-- Existential.

data ∃ (a : Set) (P : a -> Set) : Set where
  exists : {witness : a} -> P witness -> ∃ a P

∃₀ : {a : Set} (P : a -> Set) -> Set
∃₀ = ∃ _

∄ : (a : Set) (P : a -> Set) -> Set
∄ a P = ¬ (∃ a P)

∄₀ : {a : Set} (P : a -> Set) -> Set
∄₀ = ∄ _

witness : forall {a P} -> ∃ a P -> a
witness (exists {x} p) = x

proof : forall {a P} (x : ∃ a P) -> P (witness x)
proof (exists p) = p

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

{-# OPTIONS --prop #-}

open import Agda.Builtin.Nat

-- You can define datatypes in Prop, even with multiple constructors.
-- However, all constructors are considered (definitionally) equal.
data TestProp : Prop where
  p₁ p₂ : TestProp

-- Pattern matching on a datatype in Prop is disallowed unless the
-- target type is a Prop:
test-case : {P : Prop} (x₁ x₂ : P) → TestProp → P
test-case x₁ x₂ p₁ = x₁
test-case x₁ x₂ p₂ = x₂

-- All elements of a Prop are definitionally equal:
data _≡Prop_ {A : Prop} (x : A) : A → Set where
  refl : x ≡Prop x

p₁≡p₂ : p₁ ≡Prop p₂
p₁≡p₂ = refl

-- A special case are empty types in Prop: these can be eliminated to
-- any other type.
data ⊥ : Prop where

absurd : {A : Set} → ⊥ → A
absurd ()

-- We can also define record types in Prop, such as the unit:
record ⊤ : Prop  where
  constructor tt

-- We have Prop : Set₀, so we can store predicates in a small datatype:
data NatProp : Set₁ where
  c : (Nat → Prop) → NatProp

-- To define more interesting predicates, we need to define them by pattern matching:
_≤_ : Nat → Nat → Prop
zero  ≤ y     = ⊤
suc x ≤ suc y = x ≤ y
_     ≤ _     = ⊥

-- We can also define the induction principle for predicates defined in this way,
-- using the fact that we can eliminate absurd propositions with a () pattern.
≤-ind : (P : (m n : Nat) → Set)
      → (pzy : (y : Nat) → P zero y)
      → (pss : (x y : Nat) → P x y → P (suc x) (suc y))
      → (m n : Nat) → m ≤ n → P m n
≤-ind P pzy pss zero y pf = pzy y
≤-ind P pzy pss (suc x) (suc y) pf = pss x y (≤-ind P pzy pss x y pf)
≤-ind P pzy pss (suc _) zero ()

-- We can define equality as a Prop, but (currently) we cannot define
-- the corresponding eliminator, so the equality is only useful for
-- refuting impossible equations.
data _≡P_ {A : Set} (x : A) : A → Prop where
  refl : x ≡P x

0≢1 : 0 ≡P 1 → ⊥
0≢1 ()

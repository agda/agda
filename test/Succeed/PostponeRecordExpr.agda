-- Andreas, 2015-07-18
-- Postpone checking of record expressions when type is blocked.
-- Guess type of record expressions when type is blocked.

open import Common.Product
open import Common.Prelude
open import Common.Equality

T : Bool → Set
T true  = Bool × Nat
T false = ⊥

works : (P : ∀{b} → b ≡ true → T b → Set) → Set
works P = P refl record{ proj₁ = true; proj₂ = 0 }

-- Guess or postpone.
test : (P : ∀{b} → T b → b ≡ true → Set) → Set
test P = P record{ proj₁ = true; proj₂ = 0 } refl

guess : (P : ∀{b} → T b → Set) → Set
guess P = P record{ proj₁ = true; proj₂ = 0 }

record R : Set where
  field
    f : Bool

record S : Set where
  field
    f : Bool

U : Bool → Set
U true = R
U false = S

postpone : (P : ∀{b} → U b → b ≡ true → Set) → Set
postpone P = P record{ f = false } refl

-- ambiguous : (P : ∀{b} → U b → Set) → Set
-- ambiguous P = P record{ f = false }

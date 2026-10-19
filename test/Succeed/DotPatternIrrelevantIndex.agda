-- Andreas, 2026-08-28, while working on issue #8699.
-- Irrelevant dot pattern rejected without reason.
-- The corresponding Prop versions were not rejected, see
-- test/Succeed/DotPatternPropIndex.agda

{-# OPTIONS --show-irrelevant #-}

data Nat : Set where
  zero : Nat
  suc : (n : Nat) → Nat

data D : .Nat → Set where
  c : .(m : Nat) → D (suc m)

f : .(n : Nat) → D n → Set
f .(suc m) (c m) = Nat

-- WAS: rejected with error: [UnequalTerms]
-- The terms
--   suc m
-- and
--   n
-- are not equal at type Nat
-- when checking that the given dot pattern suc m matches the inferred value n

-- Should succeed.

-- In fact, any correctly typed dot pattern is acceptable in an irrelevant position.

g : .(n : Nat) → D n → Set
g .(suc (suc m)) (c m) = Nat

h : .(n : Nat) → D n → Set
h .zero (c m) = Nat

-- Should succeed.

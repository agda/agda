-- Andreas, 2026-08-28
-- Irrelevant dot pattern should not be allowed to contain arbitrary garbage.

{-# OPTIONS --show-irrelevant #-}

data Nat : Set where
  zero : Nat
  suc : (n : Nat) → Nat

data D : .Nat → Set where
  c : .(m : Nat) → D (suc m)

f : .(n : Nat) → D n → Set
f .(suc Nat) (c m) = Nat
  -- This dot pattern is garbage and should be flagged by the LHS checker,
  -- even though it is in irrelevant position.

-- Expected error: [UnequalTypes]
-- The type
--   Set
-- is not a subtype of
--   Nat
-- when checking that the expression Nat has type Nat

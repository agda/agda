-- Andreas, 2016-12-29, issue #2363

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

test : Nat → Nat
test (suc n) with zero
test zero | q = zero
test zero = zero

-- Error WAS:
-- With clause pattern zero is not an instance of its parent pattern (suc "n")

-- Expected error:
-- With clause pattern zero is not an instance of its parent pattern (suc n)

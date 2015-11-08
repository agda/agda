-- Andreas, 2014-11-08
-- This used to be a failed test case, but works now.

open import Common.Prelude

postulate
  some : Nat

data D : Nat → Set where
  d₀ : D some
  d₁ : D (suc some)

f : (n : Nat) → D n → Nat
f .some       d₀ = zero
f .(suc some) d₁ = f some d₀

-- Since  x < suc x  for all x in the structural order,
-- some < suc some  is a valid descent.

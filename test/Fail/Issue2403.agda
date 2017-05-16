-- Andreas, 2017-01-13, issue #2403

open import Common.Nat

postulate
  P : Nat → Set
  f : ∀{n} → P n → P (pred n)

test : ∀ n → P n → Set
test zero    p = Nat
test (suc n) p = test _ (f p)

-- WAS:
-- The meta-variable is solved to (pred (suc n))
-- Termination checking fails.

-- NOW: If the termination checker normalizes the argument and it passes.

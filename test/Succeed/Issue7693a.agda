open import Agda.Builtin.Nat using (zero; suc; _+_) renaming (Nat to ℕ)

mutual
  f : (n : ℕ) → ℕ
  f (suc n) = g zero (f n)
  f _ = 42

  g : (m k : ℕ) → ℕ
  g m (suc k) = g m k
  g (suc zero) k = g zero (f 42)
  g _ _ = 42

-- Used to be a termination error
-- *Arguably* should succeed

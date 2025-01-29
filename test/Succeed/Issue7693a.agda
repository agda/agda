open import Agda.Builtin.Nat using (zero; suc; _+_) renaming (Nat to ℕ)

mutual

  id : (n : ℕ) → ℕ
  id (suc n) = wks zero (id n)
  id _ = 42

  wk : (q k : ℕ) → ℕ
  wk (suc zero) k = wks zero (id 42)
  wk _ _ = 42

  wks : (q k : ℕ) → ℕ
  wks q (suc k) = wk q k
  wks _ _ = 42

-- Used to be a termination error
-- *Arguably* should succeed

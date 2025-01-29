open import Agda.Builtin.Nat using (zero; suc; _+_) renaming (Nat to ℕ)

mutual
  id : (n : ℕ) → ℕ
  id (suc n) = wks zero n n (id n)
  id _ = 42

  wk : (q n k : ℕ) → ℕ
  wk (suc zero) n k = sub zero n (suc n) k (wks zero n n (id n))
  wk _ _ _ = 42

  wks : (q m n h : ℕ) → ℕ
  wks q m (suc n) (suc h) = wk q m h + wks q m n h
  wks _ _ _ _ = 42

  sub : (q n m k l : ℕ) → ℕ
  sub q n m (suc k) l = sub q (suc n) (suc m) k (suc (wks q m n l))
  sub _ _ _ _ _ = 42

-- Used to be a termination error
-- *Arguably* should succeed

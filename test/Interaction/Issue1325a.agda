-- Andreas, 2014-10-23
-- We want to split on hidden variables.

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

f : {n : ℕ}  → Set₁
f = Set
  where
  g : {m : ℕ} → Set → Set
  g _ = {!m!}
  -- Andreas, 2016-07-10, issue 2088, changed behavior:
  -- m is made visible

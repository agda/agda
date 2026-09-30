-- Andreas, 2014-10-23
-- If you must, you can split on a shadowed hidden var...

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

f : {m m : ℕ}  → Set₁
f = Set
  where
  g : {n n : ℕ} → Set → Set
  g _ = {!n!}
  -- Andreas, 2016-07-10, issue 2088
  -- The split makes n visible (splitting can be done in next go).

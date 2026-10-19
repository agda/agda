-- Reported by stevan.andjelkovic, 2014-10-23

-- Case splitting on n in the goal g produces the wrong output, it
-- seems like {n} in f is the problem...

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

f : {_ : ℕ}  → Set₁
f {n} = Set
  where
  g : ℕ → Set
  g n = {!n!}


data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data D : Set

foo : ℕ → ℕ
foo n = n

data D where
  lam : (D → D) → D

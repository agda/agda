
data ℕ : Set where
  ze : ℕ
  su : ℕ → ℕ

f : (ℕ → ℕ) → ℕ → ℕ
f g n = g n

syntax f g n = n , g

h : ℕ
h = ?


module Issue2935 where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

bad : ℕ → ℕ
bad zero = zero
bad suc  = zero

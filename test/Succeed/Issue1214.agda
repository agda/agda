{-# OPTIONS --cubical-compatible #-}

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

Test : Set
Test = ℕ

test : Test → ℕ
test zero = zero
test (suc n) = test n

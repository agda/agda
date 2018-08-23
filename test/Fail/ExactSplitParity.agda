{-# OPTIONS --exact-split -Werror #-}

module ExactSplitParity where

data Bool : Set where
  true false : Bool

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

parity : ℕ → ℕ → Bool
parity zero          zero          = true
parity zero          (suc zero)    = false
parity zero          (suc (suc n)) = parity zero n
parity (suc zero)    zero          = false
parity (suc (suc m)) zero          = parity m zero
parity (suc m)       (suc n)       = parity m n

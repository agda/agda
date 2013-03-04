module Issue778M (Param : Set) where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

pred : Nat → Nat
pred = λ { zero → zero; (suc n) → n }
  where aux = zero



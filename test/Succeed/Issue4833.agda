module _ where

abstract
  data Nat : Set where
    Zero : Nat
    Succ : Nat → Nat

  countDown : Nat → Nat
  countDown x with x
  ... | Zero   = Zero
  ... | Succ n = countDown n

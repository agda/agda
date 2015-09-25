{-# OPTIONS --experimental-irrelevance #-}
-- {-# OPTIONS -v tc.lhs:20 #-}
module ShapeIrrelevantIndex where

data Nat : Set where
  Z : Nat
  S : Nat → Nat

data Good : ..(_ : Nat) → Set where
  goo  : .(n : Nat) → Good (S n)

bad : .(n : Nat) → Good n → Nat
bad .(S n) (goo n) = n

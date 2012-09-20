-- Andreas, 2012-09-19 propagate irrelevance info to dot patterns
{-# OPTIONS --experimental-irrelevance #-}
-- {-# OPTIONS -v tc.lhs:20 #-}
module ShapeIrrelevantIndex where

data Nat : Set where
  Z : Nat
  S : Nat → Nat

data Good : ..(_ : Nat) → Set where
  goo  : .(n : Nat) → Good (S n)

good : .(n : Nat) → Good n → Nat
good .(S n) (goo n) = Z

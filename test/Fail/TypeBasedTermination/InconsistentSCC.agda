-- During the graph processing, there is a strongly connected component that has an edge '<' within
-- (which is coming from the 'suc' in 'bar'). We should not accept such definitions
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.InconsistentSCC where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

foo : {A : Set} → (A → A) → A → A
foo f x = f x

bar : Nat → Nat
bar zero = zero
bar (suc n) = bar (foo suc n)

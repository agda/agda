-- Same as InconsistentSCC, but here the alias for successor is used
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.InconsistentSCC2 where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

s : Nat → Nat
s = suc

foo : {A : Set} → (A → A) → A → A
foo f x = f x

bar : Nat → Nat
bar zero = zero
bar (suc n) = bar (foo s n)

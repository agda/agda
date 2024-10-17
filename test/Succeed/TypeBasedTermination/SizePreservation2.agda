-- Functions are size preserving in positive positions, which includes doubly negative ones
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.SizePreservation2 where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

foo : {A : Set} → (Nat → A) → Nat → A
foo f x = f x

bar : Nat → Nat
bar zero = zero
bar (suc n) = foo bar n

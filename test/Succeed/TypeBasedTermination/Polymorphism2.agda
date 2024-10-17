-- Polymorphic signatures are naturally size-preserving 2
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.Polymorphism2 where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

foo : (∀ {A : Set} → A → A) → Nat → Nat
foo id zero = zero
foo id (suc n) = id id (foo id n)

-- Issue #7267
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.EncodingOfPostulates where

postulate
  id : {A : Set} → A → A

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

foo : Nat → Nat
foo zero = zero
foo (suc n) = foo (id n)


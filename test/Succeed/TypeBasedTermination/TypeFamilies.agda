-- Tests the handling of type families
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.TypeFamilies where

record Sigma (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

open Sigma

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

foo : Sigma Nat (λ _ → Nat) → Nat
foo (_ , zero) = zero
foo (n , suc x) = foo (n , x)

-- Tests projections of inductive records
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.BadInductiveRecords where

record R (A : Set) : Set where
  inductive
  constructor _,_
  field
    fst : A
    snd : R A

open R

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

foo : R Nat → Nat
foo r = foo (snd r)

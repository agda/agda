-- Tests the usage of constructors in a coinductive definition
-- Not allowed, because destroys strong normalization
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.BadCoinductiveConstructors2 where

record Stream (A : Set) : Set where
  constructor _,_
  coinductive
  field
    hd : A
    tl : Stream A

open Stream

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

foo2 : Stream Nat
foo2 .hd = zero
foo2 .tl = zero , (foo2 .tl)

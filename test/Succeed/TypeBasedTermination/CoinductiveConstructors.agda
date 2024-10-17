-- Tests the usage of constructors in a coinductive definition
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.CoinductiveConstructors where

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

foo : Stream Nat
foo .hd = zero
foo .tl = zero , foo

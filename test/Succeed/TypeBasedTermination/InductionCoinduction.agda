-- Tests a mix of inductive and coinductive matchings in a function
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.InductionCoinduction where

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

repeat : {A : Set} (a : A) → Nat → Stream A
hd (repeat a n) = a
tl (repeat a zero) = (repeat a (suc zero))
tl (repeat a (suc n)) = tl (repeat a n)

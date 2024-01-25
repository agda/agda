-- Tests bad interaction of inductive-coinductive definitions
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.BadInductionCoinduction where

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
tl (repeat a zero) = tl (repeat a (suc zero))
tl (repeat a (suc n)) = tl (repeat a n)

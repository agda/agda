
-- Proof irrelevance is nice when you want to work with subsets.
module Subset where

data True : Prop where
  tt : True

data False : Prop where

data (|) (A:Set)(P:A -> Prop) : Set where
  sub : (x:A) -> P x -> A | P

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

mutual
  IsEven : Nat -> Prop
  IsEven  zero   = True
  IsEven (suc n) = IsOdd n

  IsOdd : Nat -> Prop
  IsOdd  zero   = False
  IsOdd (suc n) = IsEven n

Even : Set
Even = Nat | IsEven

Odd : Set
Odd = Nat | IsOdd

(+) : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)


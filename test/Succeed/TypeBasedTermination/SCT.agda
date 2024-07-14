-- Tests from the Size-Change-Termination paper
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.SCT where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

f : Nat → Nat
g : Nat → Nat

f x = g x
g zero = zero
g (suc x) = f x

ack : Nat → Nat → Nat
ack zero    n       = suc n
ack (suc m) zero    = ack m (suc zero)
ack (suc m) (suc n) = ack m (ack (suc m) n)

perm : Nat → Nat → Nat → Nat
perm m zero    zero    = m
perm m (suc n) zero    = perm zero n m
perm m n       (suc r) = perm m    r n

f5 : Nat → Nat → Nat
f5 x       zero    = x
f5 zero    (suc y) = f5 (suc y) y
f5 (suc x) (suc y) = f5 (suc y) x

f6 : Nat → Nat → Nat
g6 : Nat → Nat → Nat
f6 a zero    = g6 a zero
f6 a (suc b) = f6 (suc a) b
g6 zero    d = d
g6 (suc c) d = g6 c (suc d)

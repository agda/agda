-- Tests a case of coinductive size preservation
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.CoinductiveSizePreservation where

record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A

open Stream

zipWith : {A B C : Set} → (A → B → C) → Stream A → Stream B → Stream C
hd (zipWith f s1 s2) = f (hd s1) (hd s2)
tl (zipWith f s1 s2) = zipWith f (tl s1) (tl s2)

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

add : Nat → Nat → Nat
add zero    y = y
add (suc x) y = suc (add x y)

fib : Stream Nat
fib .hd = zero
fib .tl .hd = suc zero
fib .tl .tl = zipWith add fib (fib .tl)

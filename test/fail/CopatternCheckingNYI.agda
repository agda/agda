{-# OPTIONS --copatterns #-}
module CopatternCheckingNYI where

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

alternate : Stream Nat
(     (head alternate)) = zero
(head (tail alternate)) = suc zero
(tail (tail alternate)) = tail alternate

-- does not yet termination-check

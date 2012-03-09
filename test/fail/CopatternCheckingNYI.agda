{-# OPTIONS --copatterns #-}
module CopatternCheckingNYI where

record Stream (A : Set) : Set where
  field
    head : A
    tail : Stream A
open Stream

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

alternate : Stream Nat
(      head alternate ) = zero
(head (tail alternate)) = suc zero
(tail (tail alternate)) = alternate
-- should parse, but type checking is not yet implemented

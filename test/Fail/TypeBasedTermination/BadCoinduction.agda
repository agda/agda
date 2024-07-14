-- Tests a non-productive coinductive function
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.BadCoinduction where

record Stream (A : Set) : Set where
  coinductive
  field
    tl : Stream A

open Stream

repeat : {A : Set} (a : A) -> Stream A
tl (repeat a) = tl (repeat a)

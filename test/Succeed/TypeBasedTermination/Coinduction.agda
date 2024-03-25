-- Tests basic usage of a coinductive stream
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.Coinduction where

record Stream (A : Set) : Set where
  coinductive
  field
    tl : Stream A

open Stream

repeat : {A : Set} (a : A) -> Stream A
tl (repeat a) = repeat a

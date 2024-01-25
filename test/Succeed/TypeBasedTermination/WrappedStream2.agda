-- Tests a coinductive copattern projection after regular copattern projection one more time
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.WrappedStream2 where

record Stream : Set where
  coinductive
  field

    tl : Stream

open Stream

record Pair (A B : Set) : Set where
  field
    p1 : A
    p2 : B

open Pair

foo : Pair Stream Stream
foo .p1 .tl = foo .p1
foo .p2 .tl = foo .p2

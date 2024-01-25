-- Tests a coinductive copattern projection after regular copattern projection
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.WrappedStream where

record Stream : Set where
  coinductive
  field tl : Stream

open Stream

record Wrapper (A : Set) : Set where
  field unwrap : A

open Wrapper

-- Stream wrapped in something
foo : Wrapper Stream
foo .unwrap .tl = foo .unwrap

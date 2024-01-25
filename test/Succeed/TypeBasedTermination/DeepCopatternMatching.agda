-- Tests deep copattern matching
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.DeepCopatternMatching where

data Unit : Set where
  unit : Unit

record Stream : Set where
  coinductive
  field
    hd : Unit
    tl : Stream

open Stream

foo : Stream → Stream
foo s .hd = s .hd
foo s .tl .hd = s .tl .hd
foo s .tl .tl = foo (s .tl .tl)

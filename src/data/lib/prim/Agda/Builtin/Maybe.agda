{-# OPTIONS --cubical-compatible --safe --no-sized-types
            --no-guardedness --level-universe --erasure #-}

module Agda.Builtin.Maybe where

data Maybe {@0 a} (A : Set a) : Set a where
  just : A → Maybe A
  nothing : Maybe A

{-# BUILTIN MAYBE Maybe #-}

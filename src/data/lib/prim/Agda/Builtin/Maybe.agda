{-# OPTIONS --cubical-compatible --safe --no-sized-types --no-guardedness --no-irrelevance --level-universe #-}

module Agda.Builtin.Maybe where

data Maybe {a} (A : Set a) : Set a where
  just : A → Maybe A
  nothing : Maybe A

{-# BUILTIN MAYBE Maybe #-}

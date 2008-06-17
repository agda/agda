
module Lib.Maybe where

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A -> Maybe A

{-# COMPILED_DATA Maybe Maybe Nothing Just #-}


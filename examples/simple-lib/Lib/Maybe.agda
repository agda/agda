
module Lib.Maybe where

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A -> Maybe A

{-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}


{-# OPTIONS --without-K #-}
module Common.Maybe where

data Maybe {a} (A : Set a) : Set a where
  nothing : Maybe A
  just    : A → Maybe A

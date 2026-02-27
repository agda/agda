{-# OPTIONS --cohesion --polarity #-}
module SharpData where

data Sharp (@♯ A : Set) : Set where
  con : (@♯ x : A) → Sharp A

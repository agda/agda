{-# OPTIONS --polarity #-}
module WrongPolarityInLambda where

f : (@++ A : Set) → Set
f = λ(@- A) → A

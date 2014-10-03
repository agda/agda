{-# OPTIONS --copatterns #-}
module Issue1290 where

record R : Set1 where
  constructor con
  field
    A : Set
open R

postulate
  X : Set

x : R
A x = X

exp : R -> R
A (exp x) = A x


{-# OPTIONS --erasure --erase-record-parameters #-}

postulate A : Set

record R (x : A) : Set where
  y : A
  y = x

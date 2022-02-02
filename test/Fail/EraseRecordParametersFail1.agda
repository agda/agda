{-# OPTIONS --erase-record-parameters #-}

postulate A : Set

record R (x : A) : Set where
  y : A
  y = x

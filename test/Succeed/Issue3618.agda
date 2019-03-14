{-# OPTIONS --prop --allow-unsolved-metas #-}

postulate
  A : Set
  P : A → Prop
  a : A
  c : P a
  Q : Prop

x : Q
x = _ where
  b : A
  b = a

  d : P b
  d = c

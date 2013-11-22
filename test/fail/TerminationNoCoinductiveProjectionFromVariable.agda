{-# OPTIONS --copatterns #-}

mutual
  data D : Set where
    c : R → D

  record R : Set where
    coinductive
    field
      out : D
open R

mutual
  d : D
  d = c r

  r : R
  out r = d

f : D → {A : Set} → A
f (c x) = f (out x)
-- should not termination check

absurd : {A : Set} → A
absurd = f d

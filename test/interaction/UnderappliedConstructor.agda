{-# OPTIONS --allow-unsolved-metas #-}
module _ where

open import Agda.Builtin.Bool

postulate
  P : Set → Set

record R : Set1 where
  constructor conR
  field
    A : Set
    B : Set

data D : Set1 where
  conD : Set → Set → D

snd : D → Set
snd (conD A B) = B


-- Eliminating from an under-applied constructor shouldn't result in a
-- crash.

F : Bool → Set₁
F = {!!}

bar : let x : F true; x = conR Bool in P (x .R.B)
bar = {!!} -- P (con Bool .R.B)

bar2 : let x : F true; x = conD Bool in P (snd x)
bar2 = {!!} -- P (snd (con Bool))

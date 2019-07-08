{-# OPTIONS --allow-unsolved-metas #-}
module _ where

open import Agda.Builtin.Bool

postulate
  P : Set → Set

record R : Set1 where
  constructor con
  field
    A : Set
    B : Set

data D : Set1 where
  con : Set → Set → D

snd : D → Set
snd (con A B) = B

-- Eliminating from an under-applied constructor shouldn't result in a
-- crash.

F : Bool → Set₁
F = {!!}

bar : let x : F true; x = R.con Bool in P (x .R.B)
bar = {!!} -- P (con Bool .R.B)

bar2 : let x : F true; x = D.con Bool in P (snd x)
bar2 = {!!} -- P (snd (con Bool))

-- These still show meta numbers because they refer to blocked
-- typechecking problems.
-- Reify could try harder to look at meta instantiations.
bar3 : let x : F true; x = D.con Bool in P (snd (x x))
bar3 = {!!} -- P (snd _23)

bar4 : let x : F true; x = (x : Bool) → Bool in P (x true)
bar4 = {!!} -- P _32

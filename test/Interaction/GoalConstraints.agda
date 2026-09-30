{-# OPTIONS --cubical #-}

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path

data Interval : Set where
  left right : Interval
  path : left ≡ right

swap : Interval → Interval
swap left = right
swap right = left
swap (path i) = {!!}

{-# OPTIONS --cubical-compatible --erasure #-}

open import Agda.Builtin.Bool

data D : Bool → Set where
  true  : D true
  false : D false

F : @0 D false → Set₁
F false = Set

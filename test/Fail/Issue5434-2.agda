{-# OPTIONS --cubical --erasure #-}

open import Agda.Builtin.Cubical.Path

data D : Set where
  c : (@0 x y : D) → x ≡ y

{-# OPTIONS --cubical #-}

open import Agda.Builtin.Cubical.Path

data I : Set where
  zero one : I
  zero≡one : zero ≡ one

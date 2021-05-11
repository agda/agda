{-# OPTIONS --cubical #-}
module Issue4365 where

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path


postulate
  A : Set
  a : A

_ : primTransp (\ i → A) i0 a ≡ a
_ = \ _ → a

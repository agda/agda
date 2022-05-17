{-# OPTIONS --cubical #-}
module Issue4365 where

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.String

postulate
  s : String

_ : primTransp (\ i → String) i0 s ≡ s
_ = \ _ → s

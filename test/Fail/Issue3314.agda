{-# OPTIONS --cubical #-}

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path

data S1 : Set where
  base : S1
  loop : base ≡ base

postulate
  weird : S1 → I

bad : (x : S1) → I
bad base     = {!!}
bad (loop x) = {!!}

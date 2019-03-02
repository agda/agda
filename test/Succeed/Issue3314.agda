{-# OPTIONS --cubical #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Cubical.Path

postulate
  admit : ∀ {A : Set} → A

data Z : Set where
  pos      : Nat → Z
  neg      : Nat → Z
  sameZero : pos 0 ≡ neg 0

_+Z_ : Z → Z → Z
pos x      +Z pos y      = admit
pos x      +Z neg y      = admit
pos x      +Z sameZero y = admit
neg x      +Z z          = admit
sameZero x +Z z          = admit

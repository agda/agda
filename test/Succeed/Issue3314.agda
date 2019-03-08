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
pos x      +Z sameZero i = admit
-- We want to allow non-full matches like the following on `neg x +Z z`
neg x      +Z z          = admit
sameZero i +Z pos x      = admit
sameZero i +Z neg x      = admit
sameZero i +Z sameZero j = admit

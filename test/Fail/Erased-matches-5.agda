-- One cannot implement []-cong directly.

{-# OPTIONS --erased-matches=restricted #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Erased.Erased
open import Agda.Primitive

private variable
  a      : Level
  @0 A   : Set a
  @0 x y : A

[]-cong : @0 x ≡ y → [ x ] ≡ [ y ]
[]-cong refl = refl

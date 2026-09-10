-- If the K rule is off, then --erased-matches without options does
-- not enable erased matches for indexed types.

{-# OPTIONS --without-K --erased-matches #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Erased.Erased
open import Agda.Primitive

private variable
  a      : Level
  @0 A   : Set
  @0 x y : A

[]-cong : @0 x ≡ y → [ x ] ≡ [ y ]
[]-cong refl = refl

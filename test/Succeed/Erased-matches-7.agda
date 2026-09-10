-- If --safe is not on, then one can enable unrestricted matches even
-- if the K rule has been disabled.

{-# OPTIONS --without-K --erased-matches=unrestricted #-}

open import Agda.Builtin.Equality

private variable
  @0 A   : Set _
  @0 x y : A

F : @0 x ≡ y → Set₁
F refl = Set

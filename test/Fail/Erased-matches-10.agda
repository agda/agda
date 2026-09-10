-- This used to be accepted, but it no longer is: the option --with-K
-- no longer overrides an explicitly given --no-erased-matches.

{-# OPTIONS --without-K --no-erased-matches --with-K #-}

open import Agda.Builtin.Equality
open import Agda.Primitive

private variable
  p      : Level
  @0 A   : Set _
  @0 x y : A

subst : (@0 P : A → Set p) → @0 x ≡ y → P x → P y
subst _ refl p = p

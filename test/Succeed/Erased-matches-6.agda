-- The option --erased-matches=unrestricted enables erased matches for
-- single-constructor data types, indexed or not.

{-# OPTIONS --erased-matches=unrestricted #-}

open import Agda.Builtin.Equality
open import Agda.Primitive

private variable
  p      : Level
  @0 A   : Set _
  @0 x y : A

data D : Set where
  c : D → D

F : @0 D → Set₁
F (c _) = Set

subst : (@0 P : A → Set p) → @0 x ≡ y → P x → P y
subst _ refl p = p

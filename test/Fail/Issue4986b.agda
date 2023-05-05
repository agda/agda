{-# OPTIONS --erasure #-}

postulate
  A : Set

open import Agda.Builtin.Equality


-- here the solution g := (\ (@0 x) (@0 y) → f y x) is not well-typed
-- in a non-erased context, which is how `g` is declared.
bar : (f : A → A → A) (g : @0 A → @0 A → A)
    → @0 _≡_ {A = @0 A → @0 A → A} g (\ (@0 x) (@0 y) → f y x)
    → @0 A → @0 A → A
bar f g refl = g

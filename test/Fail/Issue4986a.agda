{-# OPTIONS --erasure #-}

postulate
  A : Set

open import Agda.Builtin.Equality


foo : (f : A → A → A) (@0 g : @0 A → @0 A → A)
    → @0 _≡_ {A = @0 A → @0 A → A} g (\ x y → f y x)
    → @0 A → @0 A → A
foo f g refl = g
  -- In the goal, `C-c C-n g` gives
  -- λ (@0 x) (@0 y) → f y x
  -- which is only well-typed in an erased context.

bad : (f : A → A → A) → @0 A → @0 A → A
bad f = foo f (\ x y → f y x) refl

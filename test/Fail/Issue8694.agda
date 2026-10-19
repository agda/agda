{-# OPTIONS --safe #-}
-- Issue found by Claude and reported by bdrisc-ant

-- The constructor t takes its argument irrelevantly, so the conversion
-- checker identifies  t a  and  t b  for all a and b.  In particular
-- x ≡ t x  is inhabited (take x = t w; then t w ≡ t (t w) by refl), yet the
-- left-hand-side unifier reports a cycle for  x ≟ t x  and accepts the
-- absurd clause of f.

open import Agda.Builtin.Equality

data ⊥ : Set where

data T : Set where
  w : T
  t : .T → T

f : (x : T) → x ≡ t x → ⊥
f x ()

boom : ⊥
boom = f (t w) refl

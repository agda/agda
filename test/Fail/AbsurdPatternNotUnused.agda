-- Jesper, 2016-11-04
-- Absurd patterns should *not* be counted as a UnusedArg.

open import Common.Equality

data ⊥ : Set where

data Bool : Set where
  true false : Bool

abort : (A : Set) → ⊥ → A
abort A ()

test : (x y : ⊥) → abort Bool x ≡ abort Bool y
test x y = refl

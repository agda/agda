-- 2017-05-11, Reported by Ulf
-- Implicit absurd matches should be treated in the same way as explicit ones
-- when it comes to being used/unused.

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

data ⊥ : Set where
record ⊤ : Set where

abort : (A : Set) {_ : ⊥} → A
abort A {}

test : (x y : ⊥) → abort Bool {x} ≡ abort Bool {y}
test x y = refl

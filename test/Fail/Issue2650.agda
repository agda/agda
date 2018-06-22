{-# OPTIONS --cubical #-}
module _ where

module _ where
  open import Agda.Primitive.Cubical public
  open import Agda.Builtin.Cubical.Path public

  refl : ∀ {a} {A : Set a} {x : A} → x ≡ x
  refl {x = x} = \ _ → x


-- Here there's no solution for H, pattern unification will try
-- H := \ i -> b, but the equality constraints from
-- H : Path b a should rule out that assignment.
testPath : ∀ {A : Set} {b a : A} (let H : b ≡ a; H = _) → ∀ i → H i ≡ b
testPath i = refl

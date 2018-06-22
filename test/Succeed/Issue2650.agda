{-# OPTIONS --cubical #-}
module _ where

module _ where
  import Agda.Primitive
  open import Agda.Primitive.Cubical public
  open import Agda.Builtin.Cubical.Path public

  refl : ∀ {a} {A : Set a} {x : A} → x ≡ x
  refl {x = x} = \ _ → x


testPath : ∀ {A : Set} {b a : A} (let H : b ≡ b; H = _) → ∀ i → H i ≡ b
testPath i = refl

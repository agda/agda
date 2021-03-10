{-# OPTIONS --prop #-}

open import Agda.Builtin.Equality

postulate
  A : Set
  P : Prop
  p : P
  f : P → A

mutual
  X : A
  X = _

  test₁ : (x : P) → X ≡ f x
  test₁ x = refl

  test₂ : X ≡ f p
  test₂ = refl

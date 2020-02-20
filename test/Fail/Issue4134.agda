{-# OPTIONS --show-irrelevant #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

postulate
  A : Set
  f : .(Bool → A) → Bool → A

mutual
  X : .A → Bool → A
  X = _

  test : (x : Bool → A) → X (x true) ≡ f x
  test x = refl

{-# OPTIONS --cohesion #-}

open import Agda.Builtin.Equality

postulate
  A : Set

mutual
  F : ((@♭ _ : A) -> A) → A → A
  F f = _

  testF : {f : A -> A} → F f ≡ f
  testF = refl

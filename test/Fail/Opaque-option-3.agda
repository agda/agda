{-# OPTIONS --opaque #-}

open import Agda.Builtin.Equality

record R : Set₁ where
  field
    A : Set

  B : Set
  B = A

  _ : A ≡ B
  _ = refl

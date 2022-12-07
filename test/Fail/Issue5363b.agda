{-# OPTIONS --erasure #-}

open import Agda.Primitive

variable
  @0 ℓ : Level
  A : Set ℓ

levelOf : A → Level
levelOf {a} _ = a

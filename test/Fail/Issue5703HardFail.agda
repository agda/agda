{-# OPTIONS --erasure --no-eta-singleton #-}

module Issue5703HardFail where

open import Agda.Builtin.Equality

postulate
  @0 A : Set

mutual
  X : Set
  X = _

  hard-fail : X ≡ A
  hard-fail = refl

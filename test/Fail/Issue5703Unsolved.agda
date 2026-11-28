{-# OPTIONS --erasure --no-eta-singleton #-}

module Issue5703Unsolved where

open import Agda.Builtin.Equality

postulate
  @0 A : Set
  F : Set → Set

mutual
  X : Set
  X = _

  unsolved : X ≡ F A
  unsolved = refl

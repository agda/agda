{-# OPTIONS --erasure --no-eta-singleton #-}

module Issue5703ModuleParams where

open import Agda.Builtin.Equality

module _ (@0 A : Set) (F : Set → Set) where
  mutual
    X : Set
    X = _

    unsolved : X ≡ F A
    unsolved = refl

{-# OPTIONS --cumulativity #-}

open import Agda.Builtin.Equality

mutual
  X : Set
  X = _

  Y : Set₁
  Y = Set

  test : _≡_ {A = Set₁} X Y
  test = refl

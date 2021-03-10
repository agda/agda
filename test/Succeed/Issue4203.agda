
{-# OPTIONS --cumulativity #-}

open import Agda.Primitive

module _ (a ℓ : Level) where

mutual
  X : Level
  X = _

  X<=a : Set X → Set a
  X<=a A = A

  test : Set₁
  test with (lsuc ℓ)
  ... | _ = Set
    where
      a<=X : Set a → Set X
      a<=X A = A

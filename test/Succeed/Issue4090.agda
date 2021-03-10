{-# OPTIONS --cumulativity #-}

open import Agda.Primitive

postulate
  X     : Set
  P     : (A : Set) → A → Set
  id    : ∀ a (A : Set a) → A → A
  works : P (X → X) (id (lsuc lzero) X)
  fails : P _ (id (lsuc lzero) X)

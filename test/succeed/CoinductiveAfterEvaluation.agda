module CoinductiveAfterEvaluation where

open import Common.Coinduction

data Functor : Set where
  Id : Functor

_·_ : Functor → Set → Set
Id · A = A

data ν (F : Functor) : Set where
  inn : ∞ (F · ν F) → ν F

-- Evaluation is required to see that Id · ν Id is a coinductive type.

foo : ∀ F → F · ν F
foo Id = inn (♯ foo Id)

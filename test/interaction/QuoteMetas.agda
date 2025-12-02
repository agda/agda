{-# OPTIONS --quote-metas #-}

module QuoteMetas where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

macro
  m : Term → Term → TC ⊤
  m body hole = unify hole body

ex1 : ∀ ℓ (A : Set ℓ) → A → A
ex1 = m {!   !}

ex2 : ∀ ℓ (A : Set ℓ) → A → A
ex2 = m λ ℓ (A : Set ℓ) (x : A) → x

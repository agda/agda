{-# OPTIONS --quoted-holes #-}

module QuotedMetas where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

macro
  m : Term → Term → TC ⊤
  m body hole = unify hole body

ex : ∀ ℓ (A : Set ℓ) → A → A
ex = m {! !}

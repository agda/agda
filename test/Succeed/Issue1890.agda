
open import Common.Reflection

macro
  round-trip : Term → Tactic
  round-trip v hole = unify v hole

module M (A : Set) where
  data D : Set where

  test : Set
  test = round-trip D

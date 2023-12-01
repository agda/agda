module Issue6959b where

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Reflection

open Agda.Primitive

data D : Set where
  c : D

opaque
  c″ : D
  unquoteDef c″ =
    defineFun c″ (clause [] [] (con (quote c) []) ∷ [])

_ : c ≡ c″
_ = refl

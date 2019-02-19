module Issue3579 where

open import Agda.Builtin.String
open import Agda.Builtin.Reflection

data _==_ {A : Set} (a : A) : A → Set where
  refl : a == a

{-# BUILTIN EQUALITY _==_ #-}

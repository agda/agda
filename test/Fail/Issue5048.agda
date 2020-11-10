
module _ where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Equality

module M where
  open import Agda.Builtin.Nat renaming (Nat to Nombre)
  a = quote Nombre

fail : M.a ≡ quote Name
fail = refl

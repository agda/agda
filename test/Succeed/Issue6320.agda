
module _ where

open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)

macro
    fromSurface : String → Term → TC ⊤
    fromSurface s hole = do
      x <- checkFromStringTC s (def (quote Nat) [])
      unify hole x

test : Nat → Nat → Nat
test x y = fromSurface "x + y"

test≡ : test ≡ _+_
test≡ = refl

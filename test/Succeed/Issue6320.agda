
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

macro
    fromSurfaceInExtendContext : Term → TC ⊤
    fromSurfaceInExtendContext hole = do
      body <- extendContext "m"
                 (arg (arg-info visible (modality relevant quantity-0))
                      ((def (quote Nat) [])))
              (checkFromStringTC "1 + n" (def (quote Nat) []))
      unify hole (lam visible (abs "m" body))

test2 : Nat → Nat → Nat
test2 n = fromSurfaceInExtendContext

_ : test2 ≡ λ n m → suc n
_ = refl

open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Reflection

macro
  @0 trivial : Term → TC ⊤
  trivial = unify (con (quote refl) [])

test : 42 ≡ 42
test = trivial

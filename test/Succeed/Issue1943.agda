
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

-- WORKS
macro
  idT : Term → Term → TC ⊤
  idT = unify

-- FAILS
macro
  test = unify


open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Reflection

postulate
  foo : Set

macro
  bar : Term → TC ⊤
  bar = unify (def (quote foo) [])

test : Set
test = {!bar!}

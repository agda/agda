
open import Agda.Builtin.Reflection
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Equality

magic : Nat
magic = 666

macro
  by-magic : Term → TC ⊤
  by-magic hole = unify hole (def (quote magic) [])

  meta-magic : Term → TC ⊤
  meta-magic hole = unify hole (def (quote by-magic) [])

test : Nat
test = meta-magic

check : test ≡ 666
check = refl

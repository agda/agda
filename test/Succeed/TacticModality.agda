
module _ where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

variable
  A : Set

super-tac : Term → TC ⊤
super-tac hole = unify hole (lit (nat 101))

solver : Nat → Term → TC ⊤
solver n hole = unify hole (lit (nat (n + 1)))

foo : {@(tactic super-tac) n : Nat}
      {@(tactic solver n)  x : A} → A
foo  {n = n} {x = x} = x

number : Nat
number = foo

check : number ≡ 102
check = refl

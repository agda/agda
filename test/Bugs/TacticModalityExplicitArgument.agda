-- Andreas, 2023-08-22, issue #6781.
-- This is test/Succeed/TacticModality.agda, but with explicit tactic arguments.

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

-- Changing the tactic argument to visible (over test/Succeed/TacticModality.agda).

foo : (@(tactic super-tac) n : Nat)
      (@(tactic solver n)  x : A) → A
foo  n x = x

number : Nat
number = foo _ _

check : number ≡ 102
check = refl

-- This produces unsolved constraints, in contrast to the variant with hidden tactic arguments.
-- I think hiding or not should not make such a difference here.

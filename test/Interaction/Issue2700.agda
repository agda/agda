open import Agda.Builtin.Nat

record Pointed (A : Set) : Set where
 field point : A

it : ∀ {A : Set} {{x : A}} → A
it {{x}} = x

instance _ = record { point = 3 - 4 }

_ : Pointed Nat
_ = {!!}

-- Andreas, 2025-04-01, issue #7624, testcase by Szumi Xie
-- cmd_goal_type_context_check should also work if the expression introduces new metas

_ : Set
_ = {! ? !}

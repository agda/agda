-- Andreas, 2024-20-22, issue #6783
-- Error for @tactic in lambda, rather than silently dropping it.

-- {-# OPTIONS -v tc.term.lambda:30 #-}

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

super-tac : Term → TC ⊤
super-tac hole = unify hole (lit (nat 101))

bar = λ {@(tactic super-tac) n : Nat} → n + n

_ : bar ≡ 202
_ = refl

-- Expected error:

-- The @tactic attribute is not allowed here
-- when checking that the expression
-- λ {@(tactic super-tac) n : Nat} → n + n has type _4

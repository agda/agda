-- Andreas, 2024-02-20, issue #7136:
-- Error out on unsupported pattern synonym arguments.

open import Agda.Builtin.Nat

pattern p {{ x }} = suc x
-- Should be rejected: instance argument in pattern synonym not supported.
-- 2024-03-07 issue #2829: ...unless it is also an instance argument on the rhs.

pred : Nat → Nat
pred p = x
pred zero  = zero

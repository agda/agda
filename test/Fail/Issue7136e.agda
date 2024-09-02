-- Andreas, 2024-02-20, issue #7136:
-- Error out on unsupported pattern synonym arguments.

open import Agda.Builtin.Nat

pattern p (@lock x) = suc x
-- Should be rejected: cohesion attribute in pattern synonym not supported.

pred : Nat → Nat
pred (p x) = x
pred zero  = zero

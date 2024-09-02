-- Andreas, 2024-02-27, issue #7150.
-- Reported as #7113 and testcase by buggymcbugfix.
-- Regression in 2.6.4: instance search runs too late,
-- making a rewrite fail.

open import Agda.Builtin.Equality

record Semiring : Set₁ where
  field
    Carrier   : Set
    one       : Carrier
    mul       : Carrier → Carrier → Carrier
    left-unit : (r : Carrier) → mul one r ≡ r

open Semiring {{...}}

foo : {{R : Semiring}} (r : Carrier) → mul one r ≡ r
foo r rewrite left-unit r = refl

-- Andreas, 2025-09-14, issue #8103
-- Report and test case by @chiang03

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality using (_≡_)

a : (v : Bool) → v ≡ true
a v = {! v ≡ true  !}

-- C-c C-h reported an internal error
-- (observed with Agda 2.4.2.4 - 2.8.0).

-- Expected error: [Interaction.ExpectedApplication]
-- Expected an argument of the form f e1 e2 .. en
-- when checking that the expression ? has type v ≡ true

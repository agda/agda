-- Andreas, 2021-12-22, issue #5705 reported by ksqsf

open import Agda.Builtin.Equality

crash : Set ≡ Set9223372036854775808
crash = refl

-- This should fail, but crashes in Agda 2.6.2 due to Int overflow.

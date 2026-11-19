-- Andreas, 2026-11-19, issue #8933
-- Regression in 2.6.2 in the printer for floats.
-- "Integer" floats should be printed with trailing ".0"
-- so Agda can parse them back as floats.
--
-- Problem was: printing float 1.0 as just 1
-- lead to a rejection of the solution
-- computed by the constraint solver (C-c C-s).

module Issue8933 where

open import Agda.Builtin.Equality
open import Agda.Builtin.Float

test : primFloatACosh 1.0 ≡ {!!}  -- C-c C-s: primFloatACosh 1.0
test = refl

_ : 0.0 ≡ {!!}
_ = refl

_ : -0.0 ≡ {!!}
_ = refl

_ : 1.0e30 ≡ {!!}
_ = refl

-- Constraints (C-c C-=) should display with trailing ".0:
-- ?0 := 0.0
-- ?1 := 0.0
-- ?2 := -0.0
-- ?3 := 1.0e30

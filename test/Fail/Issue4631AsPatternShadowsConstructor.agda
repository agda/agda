-- Andreas, 2020-05-01, issue #4631
--
-- We should not allow @-patterns to shadow constructors!

open import Agda.Builtin.Bool

test : Set → Set
test true@_ = true

-- WAS: succees

-- EXPECTED:
--
-- Bool !=< Set
-- when checking that the expression true has type Set
--
-- ———— Warning(s) ————————————————————————————————————————————
-- Name bound in @-pattern ignored because it shadows constructor
-- when scope checking the left-hand side test true@A in the
-- definition of test

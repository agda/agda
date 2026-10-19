-- Andreas, 2026-08-24, issue #8680
-- Report and test case by Artem Shinkarov.

open import Agda.Builtin.Nat

variable
  x : Nat

pattern fails x y = suc y

-- WAS: Internal error
-- Expected error: [UnusedVariableInPatternSynonym]
-- Unused variable in pattern synonym: x
-- when scope checking the declaration
--   pattern fails x y = suc y

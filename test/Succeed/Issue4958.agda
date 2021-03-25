-- Andreas, 2020-10-11, issue #4958
-- Deprecation warning already at import statement.

open import Agda.Builtin.Float public
  renaming
    ( primFloatNumericalLess to foo )  -- Expect warning here
  using
    ( primFloatNumericalEquality )     -- Expect warning here

bar = foo -- Warning here

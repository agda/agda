-- Andreas, 2023-03-06
-- Trigger error UnusedVariableInPatternSynonym.

data D : Set where
  c : D

pattern p x = c

test : D → D
test (p x) = x

-- Expected error:
--
-- Unused variable in pattern synonym: x
-- when scope checking the declaration
--   pattern p x = c

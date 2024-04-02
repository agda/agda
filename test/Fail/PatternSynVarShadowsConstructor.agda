-- Andreas, 2023-03-06, issue #7170
-- Better error when pattern synonym parameter shadows constructor.

data D : Set where
  x : D
  c : D → D

pattern p x = c x

test : D → D
test (p x) = x

-- Error WAS:
--
-- Unused variable in pattern synonym: x
-- when scope checking the declaration
--   pattern p x = c x
--
-- Expected error:
-- Pattern synonym variable x shadows constructor defined at:
-- <<Position>>
-- when scope checking the declaration
--   pattern p x = c x

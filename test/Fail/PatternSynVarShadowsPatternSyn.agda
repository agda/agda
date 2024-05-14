-- Andreas, 2023-03-06, issue #7170
-- Better error when pattern synonym parameter shadows pattern synonym name.

data D : Set where
  z : D
  c : D → D

pattern x = z
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
--
-- Pattern synonym variable x shadows pattern synonym defined at:
-- <<Position>>
-- when scope checking the declaration
--   pattern p x = c x

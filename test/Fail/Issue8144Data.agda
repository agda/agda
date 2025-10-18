-- Andreas, 2025-10-18, issue #8144

mutual
  data D : Set where
    c : D
  open D

-- Expected error: [NoSuchModule]
-- No module D in scope---but a data type of that name is in scope
-- whose data module is either not defined yet or hidden
-- when scope checking the declaration
--   open D

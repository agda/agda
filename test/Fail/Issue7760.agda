-- Andreas, 2025-03-27 issue #7760
-- Regression introduced in 392294915fc2abdb2100f6cf8ce732941799c8da
-- as part of PR #7379

test : Set
test with Set
... | Set with Set = Set
... | x = Set

-- Expected error: [BothWithAndRHS]
-- Unexpected right hand side
-- when scope checking the declarations
--   test with Set
--   ... | Set with Set = Set
--   ... | x = Set

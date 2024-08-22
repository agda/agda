-- Andreas, 2024-08-22, trigger error ShouldBeASort

record R : Set → Set where

-- Expected error:
--
-- Set → Set should be a sort, but it isn't
-- when checking the definition of R

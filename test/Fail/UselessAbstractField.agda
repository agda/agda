{-# OPTIONS --warning=error #-}

-- Andreas, 2016-07-17

record R : Set₁ where
  abstract
    field T : Set

-- Expected error:
--
-- Using abstract here has no effect. Abstract applies only
-- definitions like data definitions, record type definitions and
-- function clauses.

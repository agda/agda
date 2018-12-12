-- {-# OPTIONS -v term:10 -v tc.pos:10 -v tc.decl:10 #-}
{-# OPTIONS --guardedness #-}

-- Andreas, 2018-02-26, issue #2975
-- Problem history:
--
-- The example below crashed with an internal error.
-- The problem is that the termination checker needs to know
-- whether force is the projection of a recursive coinductive
-- record.  However, the positivity checker has not run,
-- thus, this information is not available.

record R : Set where
  coinductive
  field force : R

  -- The following corecursive definition should pass the termination checker.
  r : R
  force r = r

-- Should succeed.

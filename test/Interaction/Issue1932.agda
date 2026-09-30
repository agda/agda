-- Andreas, 2016-04-13 display forms do not work for projection patterns

-- {-# OPTIONS -v tc.display:100 #-}

postulate B : Set

module M (A : Set) where
  record R : Set where
    field f : A

open M B

test : R
test = {!!}  -- C-c C-c RET  split on result here

-- Is:
-- M.R.f test = ?
--
-- Expected:
-- R.f test = ?

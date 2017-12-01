-- Andreas, 2017-12-01, issue #2859 introduced by parameter-refinement

-- In Agda 2.5.2 any definition by pattern matching in a module
-- with a parameter that shadows a constructor will complain
-- about pattern variables with the same name as a constructor.

-- These are pattern variables added by the parameter-refinement
-- machinery, not user written ones.  Thus, no reason to complain here.

-- {-# OPTIONS -v scope.pat:60 #-}
-- {-# OPTIONS -v tc.lhs.shadow:30 #-}

data D : Set where
  c : D

module M (c : D) where

  data DD : Set where
    cc : DD

  should-work : DD → Set
  should-work cc = DD

  should-fail : D → D
  should-fail c = c

-- Expected error:
-- The pattern variable c has the same name as the constructor c
-- when checking the clause test c = c

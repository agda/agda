-- Andreas, 2016-12-30, issue #1886

-- Make sure we do not duplicate types of parameters.

-- {-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS -v tc.data:40 -v scope.data.def:40 -v tc.decl:10 -v tc:20 #-}

data D {A : Set} (x y : {!!}) : Set where

-- Expected: only one type and one sort meta.

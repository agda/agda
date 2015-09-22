-- {-# OPTIONS -v tc.cc:30 -v tc.cover.splittree:10 #-}
-- 2013-05-03 Andreas, issue raise by Nisse.
module Issue842 where

data D : Set where
  c₁ c₂ : D

F : D → Set₁
F c₁ = Set
F = λ _ → Set

-- While not unthinkable, this is not the intended use of varying arity.
-- Since we are already splitting on the first argument, it should be
-- present on the lhs also in the second clause.

-- This will now give the error:

-- Incomplete pattern matching for F. Missing cases:
--   F c₂

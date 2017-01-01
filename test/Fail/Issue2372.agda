-- Andreas, 2017-01-01, issue #2372, reported by m0davis

-- {-# OPTIONS -v tc.def.alias:100 -v tc.decl.instance:100 #-}

-- Expected error:
-- Terms marked as eligible for instance search should end with a name
-- when checking the definition of i

postulate
  D : Set

instance
  i = D  -- NOW: Error given here (as expected).

record R : Set₁ where
  field
    r : Set

open R {{ ... }} public

f : r → Set₁ -- WAS: Here, confusingly, is where Agda registers its complaint.
f _ = Set

-- Andreas, 2017-01-21, issue #2423 overloading inherited projections

-- {-# OPTIONS -v tc.lhs.split:30 #-}
-- {-# OPTIONS -v tc.proj.amb:100 #-}
-- {-# OPTIONS -v tc.mod.apply:100 #-}

postulate
  A : Set

record R : Set where
  field f : A

record S : Set where
  field r : R
  open R r public
  -- The inherited projection (in the eyes of the scope checker) S.f
  -- is actually a composition of projections R.f ∘ S.r
  -- s .S.f = s .S.r .R.f

open S
open R

test : S → S
test s .f = s .f

-- Error WAS:
-- Cannot eliminate type S with pattern .f (did you supply too many arguments?)

-- NOW:
-- Cannot eliminate type  S  with projection  S._.f

-- Shows the chosen disambiguation in error message.

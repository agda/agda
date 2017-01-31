-- Andreas, 2017-01-21, issue #2422 overloading inherited projections

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

open R  -- works without this
open S

test : S → A
test s = f s
  -- f is not really a projection, but a composition of projections
  -- it would be nice if overloading is still allowed.

-- Error WAS:
-- Cannot resolve overloaded projection f because no matching candidate found

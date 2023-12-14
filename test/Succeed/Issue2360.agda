-- Andreas, 2016-12-28, issue #2360 reported by m0davis
-- Ambiguous projection in with-clause triggered internal error

postulate
  A : Set
  a : A

module M (X : Set) where
  record R : Set where
    field f : X

-- Opening two instantiations of M creates and ambiguous projection

open M A using (module R)
open M A

test : R
R.f test with a
R.f test | _ = a  -- WAS: triggered __IMPOSSIBLE__

-- should succeed

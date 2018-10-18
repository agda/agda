-- Andreas, 2018-10-18, issue #3289 reported by Ulf
--
-- For postfix projections, we have no hiding info
-- for the eliminated record value.

-- Thus, contrary to the prefix case, it cannot be
-- taken into account (e.g. for projection disambiguation).

open import Agda.Builtin.Nat

record R : Set where
  field
    p : Nat

open R {{...}}

test : R
test .p = 0

-- Error WAS:  Wrong hiding used for projection  R.p

-- Should work now.

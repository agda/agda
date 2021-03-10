-- Andreas, 2018-10-18, issue #3289 reported by Ulf
-- Andreas, 2021-02-10, fix rhs occurrence
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

lhs : R
lhs .p = 0

rhs : R → Nat
rhs r = r .p

-- Error WAS:  Wrong hiding used for projection  R.p

-- Should work now.

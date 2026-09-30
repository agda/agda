-- Andreas, 2014-09-03
-- Test explanation of local shadowed by import.

module _ where

module M where

  A = Set1

test : (A : Set) → let open M in {!A!}
test A = Set

-- The A exported by M is in competition with the local A.
-- Ambiguous name should be reported.

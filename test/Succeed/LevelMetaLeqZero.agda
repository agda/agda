-- Andreas, 2016-09-28, solve _ <= lzero.

-- {-# OPTIONS -v tc.conv.nat:40 #-}

open import Common.Level

data C : Set₁ where
  c : Set _ → C  -- This meta should be solved to lzero.

-- ERROR WAS:
-- Failed to solve the following constraints:
--   [0] lsuc _0 =< lsuc lzero
-- REASON:
-- Non-canonical lzero in level constraint solver

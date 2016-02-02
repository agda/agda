-- Andreas, 2016-02-02, issue reported by Nisse

record R : Set₁ where
  field F : Set

postulate r : R

open R r using (F)

S : Set
S = F

-- Run "Explain why a particular name is in scope" (C-c C-w) for F.
-- Expected result:
--
-- F is in scope as
--   * a record field Issue1804._.F brought into scope by
--     - the application of R at ...
--     - its definition at ...

-- Andreas, 2021-05-06, issue #5365
-- Error message for incomplete binding in do-block.

postulate _>>=_ : Set

test = do
  x ←

-- Expected: proper error like
--
-- Incomplete binding x ←
-- <EOF><ERROR>
-- ...

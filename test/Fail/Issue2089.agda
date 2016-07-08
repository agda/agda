-- Andreas, 2016-07-08
-- Better error message for private modules

module _ where

module M where
  private module Private where

module ShouldFail = M.Private

-- Current:
-- No such module M.Private

-- Better:
-- M.Private is not in scope since it is declared as private
-- Or (simpler):
-- M.Private exists but is not in scope here

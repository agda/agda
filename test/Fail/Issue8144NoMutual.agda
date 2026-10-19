-- Andreas, 2025-10-18, issue #8144

module _ where

module M where
  private
    module P where
      record R : Set₁ where
        field f : Set
  open P public hiding (module R)

open M
open R  -- No module R in scope

-- Expected error: [NoSuchModule]
-- No module R in scope---but a record type of that name is in scope
-- whose record module is either not defined yet or hidden (note that
-- records defined in a `mutual' block cannot be opened in the same
-- block)
-- when scope checking the declaration
--   open R

-- Part of the hint is useless here.

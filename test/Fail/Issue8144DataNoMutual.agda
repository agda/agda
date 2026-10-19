-- Andreas, 2025-10-18, issue #8144

module _ where

module M where
  private
    module P where
      data D : Set where
        c : D
  open P public hiding (module D)

open M
open D  -- No module D in scope

-- Expected error: [NoSuchModule]
-- No module D in scope---but a data type of that name is in scope
-- whose data module is either not defined yet or hidden
-- when scope checking the declaration
--   open D

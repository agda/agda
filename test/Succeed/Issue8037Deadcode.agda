-- {-# OPTIONS -v 49 #-}
-- {-# OPTIONS -v tc.mod.apply:80 #-}
{-# OPTIONS -v tc.mod.apply.complete:30 #-}

-- Andreas, 2025-11-18, issue #8037
-- The fix for #8037 involved also copying a record name
-- if one of its projections is copied in a module application.
-- It crashed because deadcode elimination had removed the record type for the projection.

-- {-# OPTIONS -v tc.mod.apply:80 #-}
-- {-# OPTIONS -v tc.mod.apply.complete:30 #-}

module Issue8037Deadcode where

import Issue8037DeadcodeA
open module A = Issue8037DeadcodeA  -- crashed with Panic: unbound name (of the record type)

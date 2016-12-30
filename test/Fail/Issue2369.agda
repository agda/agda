-- Andreas, 2016-12-30 test case for #2369

-- {-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS -v scope.import:20 #-}

module Issue2369 where

import Issue2369.OpenIP

-- Error is:

-- Module cannot be imported since it has open interaction points
-- (consider adding {-# OPTIONS --allow-unsolved-metas #-} to this
-- module)
-- when scope checking the declaration
--   import Issue2369.OpenIP

-- Error could be better, or this could just work.

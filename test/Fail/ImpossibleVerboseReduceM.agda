{-# OPTIONS -v impossible:10 #-}
-- Andreas, 2021-05-12, issue #5379
module ImpossibleVerboseReduceM where

-- Note: keep ReduceM as first word after IMPOSSIBLE!
{-# IMPOSSIBLE ReduceM should also print this debug message. #-}

-- Should print the text after IMPOSSIBLE and then raise an internal error.

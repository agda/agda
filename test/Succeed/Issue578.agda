-- 2012-03-06 Andreas
-- Errors during printing of debug messages should not propagate to the
-- top level

{-# OPTIONS -v tc.meta.assign:10 #-}
module Issue578 where

-- Skipping import of Level will leave us with no level builtins
-- import Level

data D : Set where

-- This will generate a debug message, but it cannot be printed
-- since there are no bindings for the level builtins.

-- However, the file should still succeed.

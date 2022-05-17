{-# OPTIONS -v impossible:10 #-}

module ImpossibleVerbose where

-- The only way to trigger an __IMPOSSIBLE__ that isn't a bug.
{-# IMPOSSIBLE This message should be debug-printed with option '-v impossible:10'. #-}

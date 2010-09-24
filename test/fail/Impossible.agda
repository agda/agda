-- Andreas, 2010-09-24 deactivated this annoying test case in Makefile
module Impossible where

-- The only way to trigger an __IMPOSSIBLE__ that isn't a bug.
{-# IMPOSSIBLE #-}

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP             #-}

#if  __GLASGOW_HASKELL__ > 800
{-# OPTIONS_GHC -Wno-error=missing-signatures #-}
#endif
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Internal.Utils.Monad ( tests ) where

import Agda.Utils.Monad

import Data.Functor.Identity
import Data.List (partition)

import Internal.Helpers

------------------------------------------------------------------------------

prop_partitionM_pure f xs =
  partitionM (Identity . f) xs == Identity (partition f xs)

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $allProperties work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'allProperties'.
--
-- Using 'allProperties' is convenient and superior to the manual
-- enumeration of tests, since the name of the property is added
-- automatically.

tests :: TestTree
tests = testProperties "Internal.Utils.Monad" $allProperties

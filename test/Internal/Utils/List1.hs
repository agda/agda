{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.List1 ( tests ) where

import Agda.Utils.List1 as List1

import Internal.Helpers

------------------------------------------------------------------------
-- * Properties
------------------------------------------------------------------------

prop_NonemptyList_roundtrip :: Eq a => NonEmpty a -> Bool
prop_NonemptyList_roundtrip l = maybe False (l ==) $ nonEmpty $ List1.toList l

prop_foldr_id :: List1 Int -> Bool
prop_foldr_id xs = List1.foldr (<|) singleton xs == xs

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
tests = testProperties "Internal.Utils.List1" $allProperties

{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Internal.Utils.AssocList ( tests ) where

import Agda.Utils.AssocList

import Internal.Helpers

---------------------------------------------------------------------------

type Key = Int
type Val = Int
type AL  = AssocList Key Val

prop_apply :: AL -> Key -> Bool
prop_apply m k = apply m k == lookup k m

-- In apply, the only thing to get wrong is to build the map from the list
-- in a wrong way (e.g. by naively using Map.fromList).
-- This will be wrong for duplicate keys in the association list.
--
-- Thus, test also with a small key domain to ensure lots of collisions.
prop_apply' :: AssocList Bool Val -> Bool -> Bool
prop_apply' m k = apply m k == lookup k m

---------------------------------------------------------------------------
-- * All tests
---------------------------------------------------------------------------

-- Template Haskell hack to make the following $allProperties work.
return [] -- KEEP!

-- | All tests as collected by 'allProperties'.
--
-- Using 'allProperties' is convenient and superior to the manual
-- enumeration of tests, since the name of the property is added
-- automatically.

tests :: TestTree
tests = testProperties "Internal.Utils.AssocList" $allProperties

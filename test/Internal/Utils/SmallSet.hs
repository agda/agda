{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP             #-}

#if  __GLASGOW_HASKELL__ > 800
{-# OPTIONS_GHC -Wno-error=missing-signatures #-}
#endif
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Internal.Utils.SmallSet ( tests ) where

import Data.Array (Ix)
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Utils.SmallSet (SmallSet)
import qualified Agda.Utils.SmallSet as SmallSet

import Internal.Helpers

-- Small finite set of elements
data A = A0 | A1 | A2 | A3 | A4 | A5
  deriving (Eq, Ord, Enum, Bounded, Ix, Show, Read)

instance SmallSet.SmallSetElement A

instance Arbitrary A where
  -- Ideally,
  -- arbitrary = chooseAny
  -- by then we have to implement the Random instance for A from System.Random,
  -- adding package random as direct dependency.
  arbitrary = toEnum <$> choose (fromEnum (minBound :: A), fromEnum (maxBound :: A))

-- Logical relations between SmallSet and Set

test1 :: Eq a => (SmallSet A -> a) -> (Set A -> a) -> [A] -> Bool
test1 f g as = (==) (f $ SmallSet.fromList as) (g $ Set.fromList as)

test2 :: Eq a => (SmallSet A -> SmallSet A -> a) -> (Set A -> Set A -> a) -> [A] -> [A] -> Bool
test2 f g as bs = test1 (f $ SmallSet.fromList as) (g $ Set.fromList as) bs

rel0 :: SmallSet A -> Set A -> Bool
rel0 s t = SmallSet.toList s == Set.toList t

rel1 :: (SmallSet A -> SmallSet A) -> (Set A -> Set A) -> [A] -> Bool
rel1 f g as = rel0 (f $ SmallSet.fromList as) (g $ Set.fromList as)

rel2 :: (SmallSet A -> SmallSet A -> SmallSet A) -> (Set A -> Set A -> Set A) -> [A] -> [A] -> Bool
rel2 f g as bs = rel1 (f $ SmallSet.fromList as) (g $ Set.fromList as) bs

-- Test SmallSet against Set

prop_null        = test1 (SmallSet.null)        (Set.null)
prop_member a    = test1 (SmallSet.member a)    (Set.member a)
prop_notMember a = test1 (SmallSet.notMember a) (Set.notMember a)

prop_empty       = rel0  (SmallSet.empty)       (Set.empty)
prop_singleton a = rel0  (SmallSet.singleton a) (Set.singleton a)
prop_insert a    = rel1  (SmallSet.insert a)    (Set.insert a)
prop_delete a    = rel1  (SmallSet.delete a)    (Set.delete a)

prop_union       = rel2  (SmallSet.union)       (Set.union)
prop_difference  = rel2  (SmallSet.difference)  (Set.difference)
prop_intersection= rel2  (SmallSet.intersection)(Set.intersection)


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
tests = testProperties "Internal.Utils.SmallSet" $allProperties

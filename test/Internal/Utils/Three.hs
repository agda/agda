{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.Three ( tests ) where

import Agda.Utils.Three
import Agda.Utils.Functor

import Internal.Helpers

-- | Tag the elements of the @n@th list with @n@, concatenate, partition, untag.
--   Returns the same lists.
prop_partition3_id :: [Int] -> [Int] -> [Int] -> Bool
prop_partition3_id xs ys zs =
  (xs, ys, zs) == (map snd xs', map snd ys', map snd zs')
  where
    (xs', ys', zs') = partition3 fst $ concat
      [ map (One  ,) xs
      , map (Two  ,) ys
      , map (Three,) zs
      ]

-- | Make three tagged copies of a list, shuffle (interleave only), partition, untag.
--   Returns three copies of the original list.
prop_partition3_same :: [Int] -> Bool
prop_partition3_same xs =
  (xs, xs, xs) == (map snd xs', map snd ys', map snd zs')
  where
    (xs', ys', zs') = partition3 fst $ concat
      [ [ (One, x), (Two, x), (Three, x) ] | x <- xs ]

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
tests = testProperties "Internal.Utils.Three" $allProperties

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

-- | Create clusters of non-overlapping things.

module Agda.Utils.Cluster
  ( cluster
  , cluster'
  , tests
  ) where

import Control.Monad

-- An imperative union-find library:
import Data.Equivalence.Monad

import Data.Char
import Data.Functor
import qualified Data.IntMap as Map
import Data.List

import Test.QuickCheck
import Test.QuickCheck.All
import Text.Show.Functions

-- | Characteristic identifiers.
type C = Int

-- | Given a function @f :: a -> (C,[C])@ which returns a non-empty list of
--   characteristics @C@ of @a@, partition a list of @a@s into groups
--   that share at least one characteristics.
cluster :: forall a. (a -> (C,[C])) -> [a] -> [[a]]
cluster f as = cluster' $ map (\ a -> (a, f a)) as

-- | Partition a list of @a@s paired with a non-empty list of
-- characteristics $C$ into groups that share at least one
-- characteristics.
cluster' :: forall a. [(a,(C,[C]))] -> [[a]]
cluster' acs = runEquivM id const $ do
  -- Construct the equivalence classes of characteristics.
  forM acs $ \ (_,(c,cs)) -> equateAll $ c:cs
  -- Pair each element with its class.
  cas <- forM acs $ \ (a,(c,_)) -> (`Map.singleton` [a]) <$> classDesc c
  -- Create a map from class to elements.
  let m = Map.unionsWith (++) cas
  -- Return the values of the map
  return $ Map.elems m

------------------------------------------------------------------------
-- * Properties
------------------------------------------------------------------------

-- instance Show (Int -> (C, [C])) where
--   show f = "function " ++ show (map (\ x -> (x, f x)) [-10..10])

isSingleton x = length x == 1
exactlyTwo  x = length x == 2
atLeastTwo  x = length x >= 2

prop_cluster_empty =
  null (cluster (const (0,[])) [])

prop_cluster_permutation f (as :: [Int]) =
  sort as == sort (concat (cluster f as))

prop_cluster_single a as =
  isSingleton $ cluster (const (0,[])) $ (a:as)

prop_cluster_idem f a as =
  isSingleton $ cluster f $ head $ cluster f (a:as)

prop_two_clusters (as :: [Int]) =
  atLeastTwo $ cluster (\ x -> (x, [x])) (-1:1:as)

test = cluster (\ (x:y:_) -> (ord x,[ord y]))
         ["anabel","bond","babel","hurz","furz","kurz"]
test1 = cluster (\ (x:y:_) -> (ord x,[]))
         ["anabel","bond","babel","hurz","furz","kurz"]

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $quickCheckAll work
-- under ghc-7.8.
return [] -- KEEP!

tests :: IO Bool
tests = do
  putStrLn "Agda.Utils.Cluster"
  $quickCheckAll

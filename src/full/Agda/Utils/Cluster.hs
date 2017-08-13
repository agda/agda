
-- | Create clusters of non-overlapping things.

module Agda.Utils.Cluster
  ( C
  , cluster
  , cluster'
  ) where

import Control.Monad

-- An imperative union-find library:
import Data.Equivalence.Monad

import Data.Char
import Data.Functor
import qualified Data.IntMap as IntMap

-- | Characteristic identifiers.
type C = Int

-- | Given a function @f :: a -> (C,[C])@ which returns a non-empty list of
--   characteristics @C@ of @a@, partition a list of @a@s into groups
--   such that each element in a group shares at least one characteristic
--   with at least one other element of the group.
cluster :: (a -> (C,[C])) -> [a] -> [[a]]
cluster f as = cluster' $ map (\ a -> (a, f a)) as

-- | Partition a list of @a@s paired with a non-empty list of
--   characteristics $C$ into groups
--   such that each element in a group shares at least one characteristic
--   with at least one other element of the group.
cluster' :: [(a,(C,[C]))] -> [[a]]
cluster' acs = runEquivM id const $ do
  -- Construct the equivalence classes of characteristics.
  forM_ acs $ \ (_,(c,cs)) -> equateAll $ c:cs
  -- Pair each element with its class.
  cas <- forM acs $ \ (a,(c,_)) -> (`IntMap.singleton` [a]) <$> classDesc c
  -- Create a map from class to elements.
  let m = IntMap.unionsWith (++) cas
  -- Return the values of the map
  return $ IntMap.elems m

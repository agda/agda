-- | Maps from de Bruijn indices, implemented using 'IntMap's from de
-- Bruijn levels.

module Agda.Utils.IndexMap
  (IndexMap, invariant, nil, snoc, append, fromList, update, index)
  where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.List as L

import Agda.Utils.Impossible

-- | Maps from de Bruijn indices.

-- Note that the map goes from de Bruijn *levels*.
--
-- Invariant: The map keys form a (possibly empty) contiguous range
-- from 0 upwards.

newtype IndexMap a = IndexMap { indexMap :: IntMap a }
  deriving Eq

instance Show a => Show (IndexMap a) where
  show !(IndexMap m) =
    "Agda.Utils.IndexMap.fromList " ++ show (IntMap.elems m)

-- | The 'IndexMap' invariant.

invariant :: IndexMap a -> Bool
invariant !(IndexMap m) = IntMap.keys m == [0 .. IntMap.size m - 1]

-- | Converts a de Bruijn index to a map index.

mapIndex :: IndexMap a -> Int -> Int
mapIndex !m !i = IntMap.size (indexMap m) - i - 1

-- | Is the index in range for the given map?

inRange :: Int -> IndexMap a -> Bool
inRange !i !m = 0 <= i && i < IntMap.size (indexMap m)

-- | An empty map.

nil :: IndexMap a
nil = IndexMap IntMap.empty

-- | Inserts a new binding, which will have de Bruijn index 0, and
-- shifts other bindings one step.

snoc :: IndexMap a -> a -> IndexMap a
snoc !(IndexMap m) !x = IndexMap (IntMap.insert (IntMap.size m) x m)

-- | Inserts a number of new bindings. The last element in the list
-- will have de Bruijn index 0.

append :: IndexMap a -> [a] -> IndexMap a
append !m !xs = L.foldl' snoc m xs

-- | Converts a list to an 'IndexMap'. The last element in the list
-- will have de Bruijn index 0.

fromList :: [a] -> IndexMap a
fromList = append nil

-- Overwrites a binding with the given de Bruijn index.
--
-- Precondition: The binding must already exist in the map.

update :: Int -> a -> IndexMap a -> IndexMap a
update !i !x !m
  | inRange i m = IndexMap (IntMap.insert (mapIndex m i) x (indexMap m))
  | otherwise   = __IMPOSSIBLE__

-- Looks up the thing with the given de Bruijn index.
--
-- Precondition: The index should be in range.

index :: Int -> IndexMap a -> a
index !i !m = case IntMap.lookup (mapIndex m i) (indexMap m) of
  Just x  -> x
  Nothing -> __IMPOSSIBLE__


-- | Finite bijections (implemented as a pair of tree maps).

module Agda.Utils.BiMap where

import Prelude hiding (lookup, unzip)

import Control.Applicative ((<*>))

import Data.Function
import Data.Functor
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Tuple

-- | Finite bijective map from @a@ to @b@.  There, and back again.
data BiMap a b = BiMap
  { biMapThere :: Map a b
  , biMapBack  :: Map b a
  }

-- | Lookup. O(log n).
lookup :: Ord a => a -> BiMap a b -> Maybe b
lookup a = Map.lookup a . biMapThere

-- | Inverse lookup.  O(log n).
invLookup :: Ord b => b -> BiMap a b -> Maybe a
invLookup b = Map.lookup b . biMapBack

-- | Empty bimap. O(1).
empty :: BiMap a b
empty = BiMap Map.empty Map.empty

-- | Singleton bimap. O(1).
singleton :: a -> b -> BiMap a b
singleton a b = BiMap (Map.singleton a b) (Map.singleton b a)

-- | Insert.  Overwrites existing value if present. O(Map.insert).
insert :: (Ord a, Ord b) => a -> b -> BiMap a b -> BiMap a b
insert a b (BiMap t u) = BiMap (Map.insert a b t) (Map.insert b a u)

-- | Left-biased Union. O(Map.union).
union :: (Ord a, Ord b) => BiMap a b -> BiMap a b -> BiMap a b
union (BiMap t1 b1) (BiMap t2 b2) = BiMap (Map.union t1 t2) (Map.union b1 b2)

-- | Construct from a list of pairs.
--
--   Does not check for actual bijectivity of constructed finite map. O(n log n)
fromList :: (Ord a, Ord b) => [(a,b)] -> BiMap a b
fromList = List.foldl' (flip (uncurry insert)) empty

-- | Turn into list, sorted ascendingly by first value.  O(Map.toList)
toList :: BiMap a b -> [(a,b)]
toList = Map.toAscList . biMapThere

------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------

instance (Ord a, Ord b) => Eq (BiMap a b) where
  (==) = (==) `on` biMapThere

instance (Ord a, Ord b) => Ord (BiMap a b) where
  compare = compare `on` biMapThere

instance (Show a, Show b) => Show (BiMap a b) where
  show bimap = "Agda.Utils.BiMap.fromList " ++ show (toList bimap)

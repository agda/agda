{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | A simple overlay over Data.Map to manage unordered sets with duplicates.

module Agda.Utils.Bag where

import Prelude hiding (null, map)

import Control.Applicative hiding (empty)
import Text.Show.Functions ()

import Data.Foldable (Foldable(foldMap))
import Data.Functor.Identity
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import qualified Data.Set as Set
import Data.Traversable

import Agda.Utils.Functor
import Agda.Utils.QuickCheck

#include "undefined.h"
import Agda.Utils.Impossible

-- | A set with duplicates.
--   Faithfully stores elements which are equal with regard to (==).
newtype Bag a = Bag { bag :: Map a [a] }
  deriving (Eq, Ord)
  -- The list contains all occurrences of @a@ (not just the duplicates!).
  -- Hence the invariant: the list is never empty!
  --
  -- This is slightly wasteful, but much easier to implement
  -- in terms of Map as the alternative, which is to store
  -- only the duplicates in the list.
  -- See, e.g., implementation of 'union' which would be impossible
  -- to do in the other representation.  We would need a
  -- 'Map.unionWithKey' that passes us *both* keys.
  -- But Map works under the assumption that Eq for keys is identity,
  -- it does not honor information in keys that goes beyond Ord.

------------------------------------------------------------------------
-- * Query
------------------------------------------------------------------------

null :: Bag a -> Bool
null = Map.null . bag

size :: Bag a -> Int
size = getSum . foldMap (Sum . length) . bag

-- | @bag ! a@ finds all elements equal to @a@.
(!) :: Ord a => Bag a -> a -> [a]
Bag b ! a = Map.findWithDefault [] a b

member :: Ord a => a -> Bag a -> Bool
member a = not . notMember a

notMember :: Ord a => a -> Bag a -> Bool
notMember a b = List.null (b ! a)

-- | Return the multiplicity of the given element.
count :: Ord a => a -> Bag a -> Int
count a b = length (b ! a)

------------------------------------------------------------------------
-- * Construction
------------------------------------------------------------------------

empty :: Bag a
empty = Bag $ Map.empty

singleton :: a -> Bag a
singleton a = Bag $ Map.singleton a [a]

union :: Ord a => Bag a -> Bag a -> Bag a
union (Bag b) (Bag c) = Bag $ Map.unionWith (++) b c

unions :: Ord a => [Bag a] -> Bag a
unions = Bag . Map.unionsWith (++)  . List.map bag

-- | @insert a b = union b (singleton a)@
insert :: Ord a => a -> Bag a -> Bag a
insert a = Bag . Map.insertWith (++) a [a] . bag

-- | @fromList = unions . map singleton@
fromList :: Ord a => [a] -> Bag a
fromList = Bag . Map.fromListWith (++) . List.map (\ a -> (a,[a]))

------------------------------------------------------------------------
-- * Destruction
------------------------------------------------------------------------

-- | Returns the elements of the bag, grouped by equality (==).
groups :: Bag a -> [[a]]
groups = Map.elems . bag

-- | Returns the bag, with duplicates.
toList :: Bag a -> [a]
toList = concat . groups

-- | Returns the bag without duplicates.
keys :: Bag a -> [a]
keys = Map.keys . bag
-- Works because of the invariant!
-- keys = catMaybes . map headMaybe . Map.elems . bag
--   -- Map.keys does not work, as zero copies @(a,[])@
--   -- should count as not present in the bag.

-- | Returns the bag, with duplicates.
elems :: Bag a -> [a]
elems = toList

toAscList :: Bag a -> [a]
toAscList = toList

------------------------------------------------------------------------
-- * Traversal
------------------------------------------------------------------------

map :: Ord b => (a -> b) -> Bag a -> Bag b
map f = Bag . Map.fromListWith (++) . List.map ff . Map.elems . bag
  where
    ff (a : as) = (b, b : List.map f as) where b = f a
    ff []       = __IMPOSSIBLE__

traverse' :: forall a b m . (Applicative m, Ord b) =>
             (a -> m b) -> Bag a -> m (Bag b)
traverse' f = (Bag . Map.fromListWith (++)) <.> traverse trav . Map.elems . bag
  where
    trav :: [a] -> m (b, [b])
    trav (a : as) = (\ b bs -> (b, b:bs)) <$> f a <*> traverse f as
    trav []       = __IMPOSSIBLE__

------------------------------------------------------------------------
-- * Instances
------------------------------------------------------------------------

instance Show a => Show (Bag a) where
  showsPrec _ (Bag b) = ("Agda.Utils.Bag.Bag (" ++) . showsPrec 0 b . (')':)

instance Ord a => Monoid (Bag a) where
  mempty  = empty
  mappend = union
  mconcat = unions

instance Foldable Bag where
  foldMap f = foldMap f . toList

-- not a Functor (only works for 'Ord'ered types)
-- not Traversable (only works for 'Ord'ered types)

------------------------------------------------------------------------
-- * Properties
------------------------------------------------------------------------

instance (Ord a, Arbitrary a) => Arbitrary (Bag a) where
  arbitrary = fromList <$> arbitrary

prop_count_empty :: Ord a => a -> Bool
prop_count_empty a = count a empty == 0

prop_count_singleton :: Ord a => a -> Bool
prop_count_singleton a = count a (singleton a) == 1

prop_count_insert :: Ord a => a -> Bag a -> Bool
prop_count_insert a b = count a (insert a b) == 1 + count a b

prop_size_union :: Ord a => Bag a -> Bag a -> Bool
prop_size_union b c = size (b `union` c) == size b + size c

prop_size_fromList :: Ord a => [a] -> Bool
prop_size_fromList l = size (fromList l) == length l

prop_fromList_toList :: Ord a => Bag a -> Bool
prop_fromList_toList b = fromList (toList b) == b

prop_toList_fromList :: Ord a => [a] -> Bool
prop_toList_fromList l = toList (fromList l) == List.sort l

prop_keys_fromList :: Ord a => [a] -> Bool
prop_keys_fromList l = keys (fromList l) == Set.toList (Set.fromList l)

prop_nonempty_groups :: Bag a -> Bool
prop_nonempty_groups b = all (not . List.null) $ groups b

prop_map_id :: Ord a => Bag a -> Bool
prop_map_id b = map id b == b

prop_map_compose :: (Ord b, Ord c) =>
                    (b -> c) -> (a -> b) -> Bag a -> Bool
prop_map_compose f g b = map f (map g b) == map (f . g) b

prop_traverse_id :: Ord a => Bag a -> Bool
prop_traverse_id b = traverse' Identity b == Identity b

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $quickCheckAll work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'quickCheckAll'.
--
--   Using 'quickCheckAll' is convenient and superior to the manual
--   enumeration of tests, since the name of the property is
--   added automatically.

tests :: IO Bool
tests = do
  putStrLn "Agda.Utils.Favorites"
  $quickCheckAll

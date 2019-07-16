
-- | A simple overlay over Data.Map to manage unordered sets with duplicates.

module Agda.Utils.Bag where

import Prelude hiding (null, map)

import Text.Show.Functions () -- instance only

import Data.Foldable (Foldable(foldMap))
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Semigroup

import Agda.Utils.Functor

import Agda.Utils.Impossible

-- | A set with duplicates.
--   Faithfully stores elements which are equal with regard to (==).
newtype Bag a = Bag
  { bag :: Map a [a]
      -- ^ The list contains all occurrences of @a@ (not just the duplicates!).
      --   Hence, the invariant: the list is never empty.
  }
  deriving (Eq, Ord)
  -- The list contains all occurrences of @a@ (not just the duplicates!).
  -- Hence the invariant: the list is never empty.
  --
  -- This is slightly wasteful, but much easier to implement
  -- in terms of @Map@ as the alternative, which is to store
  -- only the duplicates in the list.
  -- See, e.g., implementation of 'union' which would be impossible
  -- to do in the other representation.  We would need a
  -- 'Map.unionWithKey' that passes us *both* keys.
  -- But Map works under the assumption that Eq for keys is identity,
  -- it does not honor information in keys that goes beyond Ord.

------------------------------------------------------------------------
-- * Query
------------------------------------------------------------------------

-- | Is the bag empty?
null :: Bag a -> Bool
null = Map.null . bag

-- | Number of elements in the bag.  Duplicates count. O(n).
size :: Bag a -> Int
size = getSum . foldMap (Sum . length) . bag

-- | @(bag ! a)@ finds all elements equal to @a@.  O(log n).
--   Total function, returns @[]@ if none are.
(!) :: Ord a => Bag a -> a -> [a]
Bag b ! a = Map.findWithDefault [] a b

-- | O(log n).
member :: Ord a => a -> Bag a -> Bool
member a = not . notMember a

-- | O(log n).
notMember :: Ord a => a -> Bag a -> Bool
notMember a b = List.null (b ! a)

-- | Return the multiplicity of the given element. O(log n + count _ _).
count :: Ord a => a -> Bag a -> Int
count a b = length (b ! a)

------------------------------------------------------------------------
-- * Construction
------------------------------------------------------------------------

-- | O(1)
empty :: Bag a
empty = Bag $ Map.empty

-- | O(1)
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
-- keys = catMaybes . map listToMaybe . Map.elems . bag
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
-- Instances
------------------------------------------------------------------------

instance Show a => Show (Bag a) where
  showsPrec _ (Bag b) = ("Agda.Utils.Bag.Bag (" ++) . shows b . (')':)

instance Ord a => Semigroup (Bag a) where
  (<>) = union

instance Ord a => Monoid (Bag a) where
  mempty  = empty
  mappend = (<>)
  mconcat = unions

instance Foldable Bag where
  foldMap f = foldMap f . toList

-- not a Functor (only works for 'Ord'ered types)
-- not Traversable (only works for 'Ord'ered types)

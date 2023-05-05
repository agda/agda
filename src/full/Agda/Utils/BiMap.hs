-- | Partly invertible finite maps.
--
-- Time complexities are given under the assumption that all relevant
-- instance functions, as well as arguments of function type, take
-- constant time, and "n" is the number of keys involved in the
-- operation.

module Agda.Utils.BiMap where

import Prelude hiding (null, lookup)

import Control.Monad.Identity
import Control.Monad.State

import Data.Function (on)
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Ord
import Data.Tuple

import GHC.Generics (Generic)

import Agda.Utils.List
import Agda.Utils.Null

-- | Partial injections from a type to some tag type.
--
-- The idea is that 'tag' should be injective on its domain: if
-- @'tag' x = 'tag' y = 'Just' i@, then @x = y@. However, this
-- property does not need to hold globally. The preconditions of the
-- 'BiMap' operations below specify for which sets of values 'tag'
-- must be injective.

class HasTag a where
  type Tag a
  tag :: a -> Maybe (Tag a)

-- | Checks if the function 'tag' is injective for the values in the
-- given list for which the function is defined.

tagInjectiveFor ::
  (Eq v, Eq (Tag v), HasTag v) =>
  [v] -> Bool
tagInjectiveFor vs = and
  [ v1 == v2
  | v1 <- vs
  , v2 <- vs
  , isJust (tag v1)
  , tag v1 == tag v2
  ]

-- | Finite maps from @k@ to @v@, with a way to quickly get from @v@
-- to @k@ for certain values of type @v@ (those for which 'tag' is
-- defined).
--
-- Every value of this type must satisfy 'biMapInvariant'.

data BiMap k v = BiMap
  { biMapThere :: !(Map k v)
  , biMapBack  :: !(Map (Tag v) k)
  }
  deriving Generic

-- | The invariant for 'BiMap'.

biMapInvariant ::
  (Eq k, Eq v, Ord (Tag v), HasTag v) =>
  BiMap k v -> Bool
biMapInvariant m@(BiMap t u) =
  u ==
  Map.fromList
    [ (k', k)
    | (k, v) <- Map.toList t
    , Just k' <- [tag v]
    ]
    &&
  tagInjectiveFor (map snd $ toList m)

instance Null (BiMap k v) where
  empty = BiMap Map.empty Map.empty
  null  = null . biMapThere

-- | Is the value a source key? O(log n).

source :: Ord k => k -> BiMap k v -> Bool
source k = Map.member k . biMapThere

-- | Is the value a target key? O(log n).

target :: Ord (Tag v) => Tag v -> BiMap k v -> Bool
target k = Map.member k . biMapBack

-- | Lookup. O(log n).

lookup :: Ord k => k -> BiMap k v -> Maybe v
lookup a = Map.lookup a . biMapThere

-- | Inverse lookup. O(log n).

invLookup :: Ord (Tag v) => Tag v -> BiMap k v -> Maybe k
invLookup k = Map.lookup k . biMapBack

-- | Singleton map. O(1).

singleton :: HasTag v => k -> v -> BiMap k v
singleton k v =
  BiMap
    (Map.singleton k v)
    (case tag v of
       Nothing -> Map.empty
       Just k' -> Map.singleton k' k)

-- | Insertion. Overwrites existing values. O(log n).
--
-- Precondition: See 'insertPrecondition'.

insert ::
  (Ord k, HasTag v, Ord (Tag v)) =>
  k -> v -> BiMap k v -> BiMap k v
insert k v (BiMap t b) =
  BiMap
    (Map.insert k v t)
    (case tag v of
       Nothing -> b'
       Just k' -> Map.insert k' k b')
  where
  b' = case tag =<< Map.lookup k t of
    Nothing -> b
    Just k' -> Map.delete k' b

-- | The precondition for @'insert' k v m@: If @v@ has a 'tag' (@'tag'
-- v ≠ 'Nothing'@), then @m@ must not contain any mapping @k' ↦ v'@
-- for which @k ≠ k'@ and @'tag' v = 'tag' v'@.

insertPrecondition ::
  (Eq k, Eq v, Eq (Tag v), HasTag v) =>
  k -> v -> BiMap k v -> Bool
insertPrecondition k v m =
  case tag v of
    Nothing -> True
    Just _  ->
      not $ any (\(k', v') -> k' /= k && tag v == tag v') $ toList m

-- | Modifies the value at the given position, if any. If the function
-- returns 'Nothing', then the value is removed. O(log n).
--
-- The precondition for @'alterM' f k m@ is that, if the value @v@ is
-- inserted into @m@, and @'tag' v@ is defined, then no key other than
-- @k@ may map to a value @v'@ for which @'tag' v' = 'tag' v@.

alterM ::
  forall k v m. (Ord k, Ord (Tag v), HasTag v, Monad m) =>
  (Maybe v -> m (Maybe v)) -> k -> BiMap k v -> m (BiMap k v)
alterM f k m@(BiMap t b) = do
  (t', r) <- runStateT (Map.alterF f' k t) Nothing
  return $ case r of
    Nothing -> m
    Just r  -> BiMap t' (updateBack r b)
  where
  f' ::
    Maybe v ->
    StateT (Maybe (Maybe (Tag v), Maybe (Tag v))) m (Maybe v)
  f' v = do
    r <- lift (f v)
    put $ Just (tag =<< v, tag =<< r)
    return r

  updateBack (k'1, k'2) =
    if k'1 == k'2
    then id
    else maybe id (flip Map.insert k) k'2 .
         maybe id Map.delete k'1

-- | Modifies the value at the given position, if any. If the function
-- returns 'Nothing', then the value is removed. O(log n).
--
-- Precondition: See 'alterPrecondition'.

alter ::
  forall k v. (Ord k, Ord (Tag v), HasTag v) =>
  (Maybe v -> Maybe v) -> k -> BiMap k v -> BiMap k v
alter f k m = runIdentity $ alterM (Identity . f) k m

-- | The precondition for @'alter' f k m@ is that, if the value @v@ is
-- inserted into @m@, and @'tag' v@ is defined, then no key other than
-- @k@ may map to a value @v'@ for which @'tag' v' = 'tag' v@.

alterPrecondition ::
  (Ord k, Eq v, Eq (Tag v), HasTag v) =>
  (Maybe v -> Maybe v) -> k -> BiMap k v -> Bool
alterPrecondition f k m =
  case tag =<< f (lookup k m) of
    Nothing -> True
    Just k' -> and
      [ Just k' /= tag v
      | (k'', v) <- toList m
      , k'' /= k
      ]

-- | Modifies the value at the given position, if any. If the function
-- returns 'Nothing', then the value is removed. O(log n).
--
-- Precondition: See 'updatePrecondition'.

update ::
  (Ord k, Ord (Tag v), HasTag v) =>
  (v -> Maybe v) -> k -> BiMap k v -> BiMap k v
update f = alter (f =<<)

-- | The precondition for @'update' f k m@ is that, if the value @v@
-- is inserted into @m@, and @'tag' v@ is defined, then no key other
-- than @k@ may map to a value @v'@ for which @'tag' v' = 'tag' v@.

updatePrecondition ::
  (Ord k, Eq v, Eq (Tag v), HasTag v) =>
  (v -> Maybe v) -> k -> BiMap k v -> Bool
updatePrecondition f = alterPrecondition (f =<<)

-- | Modifies the value at the given position, if any. O(log n).
--
-- Precondition: See 'adjustPrecondition'.

adjust ::
  (Ord k, Ord (Tag v), HasTag v) =>
  (v -> v) -> k -> BiMap k v -> BiMap k v
adjust f = update (Just . f)

-- | The precondition for @'adjust' f k m@ is that, if the value @v@
-- is inserted into @m@, and @'tag' v@ is defined, then no key other
-- than @k@ may map to a value @v'@ for which @'tag' v' = 'tag' v@.

adjustPrecondition ::
  (Ord k, Eq v, Eq (Tag v), HasTag v) =>
  (v -> v) -> k -> BiMap k v -> Bool
adjustPrecondition f = updatePrecondition (Just . f)

-- | Inserts a binding into the map. If a binding for the key already
-- exists, then the value obtained by applying the function to the
-- key, the new value and the old value is inserted, and the old value
-- is returned.
--
-- Precondition: See 'insertLookupWithKeyPrecondition'.

insertLookupWithKey ::
  forall k v. (Ord k, Ord (Tag v), HasTag v) =>
  (k -> v -> v -> v) -> k -> v -> BiMap k v -> (Maybe v, BiMap k v)
insertLookupWithKey f k v m = swap $ runState (alterM f' k m) Nothing
  where
  f' :: Maybe v -> State (Maybe v) (Maybe v)
  f' Nothing     = return $ Just v
  f' r@(Just v') = do
    put r
    return $ Just (f k v v')

-- | The precondition for @'insertLookupWithKey' f k v m@ is that, if
-- the value @v'@ is inserted into @m@, and @'tag' v'@ is defined,
-- then no key other than @k@ may map to a value @v''@ for which
-- @'tag' v'' = 'tag' v'@.

insertLookupWithKeyPrecondition ::
  (Ord k, Eq v, Eq (Tag v), HasTag v) =>
  (k -> v -> v -> v) -> k -> v -> BiMap k v -> Bool
insertLookupWithKeyPrecondition f k v =
  alterPrecondition (Just . maybe v (f k v)) k

-- | Changes all the values using the given function, which is also
-- given access to keys. O(n log n).
--
-- Precondition: See 'mapWithKeyPrecondition'.

mapWithKey ::
  (Ord k, Ord (Tag v), HasTag v) =>
  (k -> v -> v) -> BiMap k v -> BiMap k v
mapWithKey f = fromList . map (\(k, v) -> (k, f k v)) . toList

-- | The precondition for @'mapWithKey' f m@: For any two distinct
-- mappings @k₁ ↦ v₁@, @k₂ ↦ v₂@ in @m@ for which the tags of
-- @f k₁ v₁@ and @f k₂ v₂@ are defined the values of @f@ must be
-- distinct (@f k₁ v₁ ≠ f k₂ v₂@). Furthermore 'tag' must be injective
-- for @{ f k v | (k, v) ∈ m }@.

mapWithKeyPrecondition ::
  (Eq k, Eq v, Eq (Tag v), HasTag v) =>
  (k -> v -> v) -> BiMap k v -> Bool
mapWithKeyPrecondition f =
  fromListPrecondition . map (\(k, v) -> (k, f k v)) . toList

-- | Changes all the values using the given function, which is also
-- given access to keys. O(n).
--
-- Precondition: See 'mapWithKeyFixedTagsPrecondition'. Note that tags
-- must not change.

mapWithKeyFixedTags :: (k -> v -> v) -> BiMap k v -> BiMap k v
mapWithKeyFixedTags f (BiMap t b) = BiMap (Map.mapWithKey f t) b

-- | The precondition for @'mapWithKeyFixedTags' f m@ is that, if @m@
-- maps @k@ to @v@, then @'tag' (f k v) == 'tag' v@.

mapWithKeyFixedTagsPrecondition ::
  (Eq v, Eq (Tag v), HasTag v) =>
  (k -> v -> v) -> BiMap k v -> Bool
mapWithKeyFixedTagsPrecondition f m = and
  [ tag (f k v) == tag v
  | (k, v) <- toList m
  ]

-- | Left-biased union. For the time complexity, see 'Map.union'.
--
-- Precondition: See 'unionPrecondition'.

union :: (Ord k, Ord (Tag v)) => BiMap k v -> BiMap k v -> BiMap k v
union (BiMap t1 b1) (BiMap t2 b2) =
  BiMap (Map.union t1 t2) (Map.union b1 b2)

-- The precondition for @'union' m₁ m₂@: If @k@ is mapped to @v₁@ in
-- @m₁@ and @v₂@ in @m₂@, then @'tag' v₂ = 'Nothing'@ or @'tag' v₁ =
-- 'tag' v₂@. Furthermore, if @k₁@ is mapped to @v₁@ in @m₁@ and @k₂@
-- is mapped to @v₂@ in @m₂@, where @'tag' v₁ = 'tag' v₂ = 'Just' k@,
-- then @k₁ = k₂@. Finally 'tag' must be injective for
-- @{v₁ | (k₁, v₁) ∈ m₁} ∪ {v₂ | (k₂, v₂) ∈ m₂, k₂ ∉ m₁}@.

unionPrecondition ::
  (Ord k, Eq v, Eq (Tag v), HasTag v) =>
  BiMap k v -> BiMap k v -> Bool
unionPrecondition m1@(BiMap t1 _) m2@(BiMap t2 _) =
  and
    [ tag v2 == Nothing || tag v1 == tag v2
    | (v1, v2) <- Map.elems $ Map.intersectionWith (,) t1 t2
    ] &&
  and
    [ k1 == k2
    | (k1, v1) <- toList m1
    , (k2, v2) <- toList m2
    , tag v1 == tag v2
    , isJust (tag v1)
    ]
    &&
  tagInjectiveFor
    ([ v1
     | (_, v1) <- toList m1
     ] ++
     [ v2
     | (k2, v2) <- toList m2
     , not (k2 `elem` ks1)
     ])
  where
  ks1 = map fst (toList m1)

-- | Conversion from lists of pairs. Later entries take precedence
-- over earlier ones. O(n log n).
--
-- Precondition: See 'fromListPrecondition'.

fromList ::
  (Ord k, Ord (Tag v), HasTag v) =>
  [(k, v)] -> BiMap k v
fromList = List.foldr (uncurry insert) empty

-- The precondition for @'fromList' kvs@: For all pairs @(k₁, v₁)@,
-- @(k₂, v₂)@ in @kvs@ for which the tags of @v₁@ and @v₂@ are
-- defined, if @v₁ = v₂@ then @k₁ = k₂@. Furthermore 'tag' must be
-- injective for the values in the list.

fromListPrecondition ::
  (Eq k, Eq v, Eq (Tag v), HasTag v) =>
  [(k, v)] -> Bool
fromListPrecondition kvs =
  and
    [ k1 == k2
    | (k1, v1) <- kvs
    , (k2, v2) <- kvs
    , isJust (tag v1)
    , isJust (tag v2)
    , v1 == v2
    ]
    &&
  tagInjectiveFor (map snd kvs)

-- | Conversion to lists of pairs, with the keys in ascending order.
-- O(n).

toList :: BiMap k v -> [(k, v)]
toList = Map.toAscList . biMapThere

-- | The keys, in ascending order. O(n).

keys :: BiMap k v -> [k]
keys = Map.keys . biMapThere

-- | The values, ordered according to the corresponding keys. O(n).

elems :: BiMap k v -> [v]
elems = Map.elems . biMapThere

-- | Conversion from two lists that contain distinct keys/tags, with
-- the keys/tags in ascending order. O(n).
--
-- Precondition: See 'fromDistinctAscendingListsPrecondition'.

fromDistinctAscendingLists ::
  ([(k, v)], [(Tag v, k)]) -> BiMap k v
fromDistinctAscendingLists (t, b) =
  BiMap (Map.fromDistinctAscList t) (Map.fromDistinctAscList b)

-- The precondition for @'fromDistinctAscendingLists' (kvs, kks)@: The
-- lists must contain distinct keys/tags, and must be sorted according
-- to the keys/tags. Furthermore, for every pair @(k, v)@ in the first
-- list for which @'tag' v = 'Just' k'@ there must be a pair @(k', k)@
-- in the second list, and there must not be any other pairs in that
-- list. Finally 'tag' must be injective for @{v | (_, v) ∈ kvs }@.

fromDistinctAscendingListsPrecondition ::
  (Ord k, Eq v, Ord (Tag v), HasTag v) =>
  ([(k, v)], [(Tag v, k)]) -> Bool
fromDistinctAscendingListsPrecondition (kvs, kks) =
  fastDistinct (map fst kvs) && sorted (map fst kvs)
    &&
  fastDistinct (map fst kks) && sorted (map fst kks)
    &&
  kks ==
  List.sortBy (comparing fst)
    [ (k', k)
    | (k, v) <- kvs
    , Just k' <- [tag v]
    ]
    &&
  tagInjectiveFor [ v | (_, v) <- kvs ]

-- | Generates input suitable for 'fromDistinctAscendingLists'. O(n).

toDistinctAscendingLists :: BiMap k v -> ([(k, v)], [(Tag v, k)])
toDistinctAscendingLists (BiMap t b) =
  (Map.toAscList t, Map.toAscList b)

------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------

instance (Eq k, Eq v) => Eq (BiMap k v) where
  (==) = (==) `on` biMapThere

instance (Ord k, Ord v) => Ord (BiMap k v) where
  compare = compare `on` biMapThere

instance (Show k, Show v) => Show (BiMap k v) where
  show bimap = "Agda.Utils.BiMap.fromList " ++ show (toList bimap)

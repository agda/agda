
-- | Constructing singleton collections.

module Agda.Utils.Singleton where

import Data.Maybe
import Data.Monoid (Endo(..))

import Data.DList (DList)
import qualified Data.DList as DL
import Data.Hashable (Hashable)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.List.NonEmpty (NonEmpty(..))

import Data.EnumMap (EnumMap)
import qualified Data.EnumMap as EnumMap
import Data.EnumSet (EnumSet)
import qualified Data.EnumSet as EnumSet
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Set.NonEmpty (NESet)
import qualified Data.Set.NonEmpty as Set1

import Agda.Utils.Null     (Null, empty)
import Agda.Utils.SmallSet (SmallSet, SmallSetElement)
import qualified Agda.Utils.SmallSet as SmallSet
import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as VarSet

-- | A create-only possibly empty collection is a monoid with the possibility
--   to inject elements.

class (Semigroup coll, Monoid coll, Singleton el coll) => Collection el coll
    | coll -> el where
  fromList :: [el] -> coll
  fromList = mconcat . map singleton

instance Collection a        [a]          where
  fromList = id
  {-# INLINE fromList #-}
instance Collection a        ([a] -> [a]) where
  fromList = (++)
  {-# INLINE fromList #-}
instance Collection a        (Endo [a])   where
  fromList = Endo . fromList
  {-# INLINE fromList #-}
instance Collection a        (DList a)    where
  fromList = DL.fromList
  {-# INLINE fromList #-}
instance Collection a        (Seq a)      where
  fromList = Seq.fromList
  {-# INLINE fromList #-}
instance Collection Int      IntSet       where
  fromList = IntSet.fromList
  {-# INLINE fromList #-}
instance Collection (Int, a) (IntMap a)   where
  fromList = IntMap.fromList
  {-# INLINE fromList #-}

instance Enum k             => Collection k      (EnumSet k)   where
  fromList = EnumSet.fromList
  {-# INLINE fromList #-}
instance Enum k             => Collection (k, a) (EnumMap k a) where
  fromList = EnumMap.fromList
  {-# INLINE fromList #-}
instance (Eq k, Hashable k) => Collection k      (HashSet k)   where
  fromList = HashSet.fromList
  {-# INLINE fromList #-}
instance (Eq k, Hashable k) => Collection (k, a) (HashMap k a) where
  fromList = HashMap.fromList
  {-# INLINE fromList #-}
instance Ord k              => Collection k      (Set k)       where
  fromList = Set.fromList
  {-# INLINE fromList #-}
instance Ord k              => Collection (k, a) (Map k a)     where
  fromList = Map.fromList
  {-# INLINE fromList #-}
instance SmallSetElement k  => Collection k      (SmallSet k)  where
  fromList = SmallSet.fromList
  {-# INLINE fromList #-}

-- | Create-only collection with at most one element.

class (Null coll, Singleton el coll) => CMaybe el coll | coll -> el where
  cMaybe :: Maybe el -> coll
  cMaybe = maybe empty singleton

instance CMaybe a (Maybe a) where cMaybe = id
instance CMaybe a [a]       where cMaybe = maybeToList

-- | Overloaded @singleton@ constructor for collections.

class Singleton el coll | coll -> el where
  singleton :: el -> coll

instance Singleton a   (Maybe a)    where
  singleton = Just
  {-# INLINE singleton #-}
instance Singleton a   [a]          where
  singleton = (:[])
  {-# INLINE singleton #-}
instance Singleton a   ([a] -> [a]) where
  singleton = (:)
  {-# INLINE singleton #-}
instance Singleton a   (Endo [a])   where
  singleton = Endo . (:)
  {-# INLINE singleton #-}
instance Singleton a   (DList a)    where
  singleton = DL.singleton
  {-# INLINE singleton #-}
instance Singleton a   (NESet a)    where
  singleton = Set1.singleton
  {-# INLINE singleton #-}
instance Singleton a   (NonEmpty a) where
  singleton = (:| [])
  {-# INLINE singleton #-}
instance Singleton a   (Seq a)      where
  singleton = Seq.singleton
  {-# INLINE singleton #-}
instance Singleton a   (Set a)      where
  singleton = Set.singleton
  {-# INLINE singleton #-}
instance Singleton Int IntSet       where
  singleton = IntSet.singleton
  {-# INLINE singleton #-}
instance Singleton Int VarSet       where
  singleton = VarSet.singleton
  {-# INLINE singleton #-}

instance Enum a            => Singleton a (EnumSet  a) where
  singleton = EnumSet.singleton
  {-# INLINE singleton #-}
instance SmallSetElement a => Singleton a (SmallSet a) where
  singleton = SmallSet.singleton
  {-# INLINE singleton #-}

instance Singleton (k  ,a) (Map  k a)                  where
  singleton = uncurry Map.singleton
  {-# INLINE singleton #-}
instance Singleton (Int,a) (IntMap a)                  where
  singleton = uncurry IntMap.singleton
  {-# INLINE singleton #-}

instance Hashable k => Singleton k     (HashSet   k)   where
  singleton = HashSet.singleton
  {-# INLINE singleton #-}
instance Hashable k => Singleton (k,a) (HashMap k a)   where
  singleton = uncurry HashMap.singleton
  {-# INLINE singleton #-}
instance Enum k     => Singleton (k,a) (EnumMap k a)   where
  singleton = uncurry EnumMap.singleton
  {-# INLINE singleton #-}

-- Testing newtype-deriving:

-- newtype Wrap c = Wrap c
--   deriving (Singleton k)  -- Succeeds

-- Type family version:

-- class Singleton c where
--   type Elem c
--   singleton :: Elem c -> c

-- instance Singleton [a] where
--   type Elem [a] = a
--   singleton = (:[])

-- instance Singleton (Maybe a) where
--   type Elem (Maybe a) = a
--   singleton = Just

-- instance Singleton (Set a) where
--   type Elem (Set a) = a
--   singleton = Set.singleton

-- instance Singleton (Map k a) where
--   type Elem (Map k a) = (k,a)
--   singleton = uncurry Map.singleton

-- newtype Wrap a = Wrap a
--   deriving (Singleton)  -- Fails

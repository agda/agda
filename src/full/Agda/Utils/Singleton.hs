{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- {-# LANGUAGE TypeFamilies #-}

-- | Constructing singleton collections.

module Agda.Utils.Singleton where

import Data.Monoid (Endo(..))

import Data.Hashable (Hashable)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet

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

import Agda.Utils.NonemptyList (NonemptyList((:!)))

class Singleton el coll | coll -> el where
  singleton :: el -> coll

instance Singleton a   (Maybe a)   where singleton = Just
instance Singleton a   [a]         where singleton = (:[])
instance Singleton a  ([a] -> [a]) where singleton = (:)
instance Singleton a   (Endo [a])  where singleton = Endo . (:)
instance Singleton a   (NonemptyList a)
                                   where singleton = (:! [])
instance Singleton a   (Seq a)     where singleton = Seq.singleton
instance Singleton a   (Set a)     where singleton = Set.singleton
instance Singleton Int IntSet      where singleton = IntSet.singleton

instance Singleton (k  ,a) (Map  k a) where singleton = uncurry Map.singleton
instance Singleton (Int,a) (IntMap a) where singleton = uncurry IntMap.singleton

instance Hashable a => Singleton a     (HashSet   a) where singleton = HashSet.singleton
instance Hashable k => Singleton (k,a) (HashMap k a) where singleton = uncurry HashMap.singleton

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

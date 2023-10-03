{-# OPTIONS_GHC -Wunused-imports #-}

------------------------------------------------------------------------
-- | Hash tables.
------------------------------------------------------------------------

module Agda.Utils.HashTable
  ( HashTable
  , empty
  , insert
  , lookup
  , toList
  , keySet
  ) where

import Prelude hiding (lookup)

import Data.Hashable
import qualified Data.Vector.Hashtables as H
import qualified Data.Vector.Mutable as VM
import qualified Data.Vector as V
import Data.Set (Set)
import qualified Data.Set as Set

-- | Hash tables.

-- A very limited amount of (possibly outdated) testing indicates
-- that, for the use in Agda's serialiser/deserialiser,
-- Data.HashTable.IO.CuckooHashTable is somewhat slower than
-- Data.HashTable.IO.BasicHashTable, and that
-- Data.HashTable.IO.LinearHashTable and the hashtables from
-- Data.Hashtable are much slower. However, other (also possibly
-- outdated) testing suggests that Data.HashTable.IO.CuckooHashTable
-- is quite a bit faster than Data.HashTable.IO.BasicHashTable for
-- 64-bit Windows. Some more recent, also limited, testing suggests
-- that the following hash table implementation from
-- Data.Vector.Hashtables is quite a bit faster than
-- Data.HashTable.IO.BasicHashTable (see issue #5966).

newtype HashTable k v =
  HashTable (H.Dictionary (H.PrimState IO) VM.MVector k VM.MVector v)

-- | An empty hash table.

empty :: IO (HashTable k v)
empty = HashTable <$> H.initialize 0

-- | Inserts the key and the corresponding value into the hash table.

insert :: (Eq k, Hashable k) => HashTable k v -> k -> v -> IO ()
insert (HashTable h) = H.insert h
{-# INLINABLE insert #-}

-- | Tries to find a value corresponding to the key in the hash table.

lookup :: (Eq k, Hashable k) => HashTable k v -> k -> IO (Maybe v)
lookup (HashTable h) = H.lookup h
{-# INLINABLE lookup #-}

-- | Converts the hash table to a list.
--
-- The order of the elements in the list is unspecified.

toList :: (Eq k, Hashable k) => HashTable k v -> IO [(k, v)]
toList (HashTable h) = H.toList h
{-# INLINABLE toList #-}

keySet :: forall k v. Ord k => HashTable k v -> IO (Set k)
keySet (HashTable h) = do
  (ks :: V.Vector k) <- H.keys h
  pure $! V.foldl' (flip Set.insert) mempty ks
{-# INLINABLE keySet #-}

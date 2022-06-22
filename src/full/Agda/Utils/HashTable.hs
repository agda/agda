------------------------------------------------------------------------
-- | Hash tables.
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module Agda.Utils.HashTable
  ( HashTable
  , empty
  , insert
  , lookup
  , toList
  ) where

import Prelude hiding (lookup)

import Data.Hashable
import qualified Data.HashTable.IO as H

-- | Hash tables.

-- A very limited amount of (possibly outdated) testing indicates
-- that, for the use in Agda's serialiser/deserialiser,
-- Data.HashTable.IO.CuckooHashTable is somewhat slower than
-- Data.HashTable.IO.BasicHashTable, and that
-- Data.HashTable.IO.LinearHashTable and the hashtables from
-- Data.Hashtable are much slower. However, other (also possibly
-- outdated) testing suggests that Data.HashTable.IO.CuckooHashTable
-- is quite a bit faster than Data.HashTable.IO.BasicHashTable for
-- 64-bit Windows.

newtype HashTable k v = HashTable
#if defined(mingw32_HOST_OS) && defined(x86_64_HOST_ARCH)
  (H.CuckooHashTable k v)
#else
  (H.BasicHashTable k v)
#endif

-- | An empty hash table.

empty :: IO (HashTable k v)
empty = HashTable <$> H.new

-- | Inserts the key and the corresponding value into the hash table.

insert :: (Eq k, Hashable k) => HashTable k v -> k -> v -> IO ()
insert (HashTable h) = H.insert h

-- | Tries to find a value corresponding to the key in the hash table.

lookup :: (Eq k, Hashable k) => HashTable k v -> k -> IO (Maybe v)
lookup (HashTable h) = H.lookup h

-- | Converts the hash table to a list.
--
-- The order of the elements in the list is unspecified.

toList :: (Eq k, Hashable k) => HashTable k v -> IO [(k, v)]
toList (HashTable h) = H.toList h

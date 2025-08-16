{-# LANGUAGE Strict #-}
{-# OPTIONS_GHC -Wunused-imports -Wno-redundant-bang-patterns #-}

------------------------------------------------------------------------
-- | Hash tables.
------------------------------------------------------------------------

module Agda.Utils.HashTable
  ( HashTable
  , HashTableLU
  , HashTableLL
  , Agda.Utils.HashTable.empty
  , Agda.Utils.HashTable.insert
  , Agda.Utils.HashTable.lookup
  , Agda.Utils.HashTable.toList
  , forAssocs
  , Agda.Utils.HashTable.size
  , insertingIfAbsent
  ) where

import Prelude hiding (lookup)

import Data.Bits
import Data.Hashable
import Data.Primitive.MutVar
import Data.Vector.Hashtables
import Data.Vector.Hashtables.Internal
import Data.Vector.Hashtables.Internal.Mask

import qualified Data.Primitive.PrimArray as A

import Data.Vector.Generic.Mutable (MVector)
import qualified Data.Vector.Mutable as VM
import qualified Data.Vector.Unboxed.Mutable as VUM

import Agda.Utils.Monad


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

newtype HashTable ks k vs v =
  HashTable (Dictionary (PrimState IO) ks k vs v)

-- | Hashtable with lifted keys and unboxed values.
type HashTableLU k v = HashTable VM.MVector k VUM.MVector v

-- | Hashtable with lifted keys and lifted values.
type HashTableLL k v = HashTable VM.MVector k VM.MVector v

-- | An empty hash table.

empty :: (MVector ks k, MVector vs v) => IO (HashTable ks k vs v)
empty = HashTable <$!> initialize 0

-- | Inserts the key and the corresponding value into the hash table.

insert :: (Hashable k, MVector vs v, MVector ks k) =>
          HashTable ks k vs v -> k -> v -> IO ()
insert (HashTable h) = Data.Vector.Hashtables.insert h
{-# INLINABLE insert #-}

-- | Tries to find a value corresponding to the key in the hash table.

lookup :: (Hashable k, MVector ks k, MVector vs v)
       => HashTable ks k vs v -> k -> IO (Maybe v)
lookup (HashTable h) = Data.Vector.Hashtables.lookup h
{-# INLINABLE lookup #-}

-- | Converts the hash table to a list.
--
-- The order of the elements in the list is unspecified.

toList :: (Hashable k, MVector ks k, MVector vs v) => HashTable ks k vs v -> IO [(k, v)]
toList (HashTable h) = Data.Vector.Hashtables.toList h
{-# INLINABLE toList #-}

-- | Iterate over key-value pairs in IO.
forAssocs :: (MVector ks k, MVector vs v)
          => HashTable ks k vs v -> (k -> v -> IO ()) -> IO ()
forAssocs (HashTable h) f = do
  Dictionary{..} <- readMutVar (getDRef h)
  count <- refs ! getCount
  let go :: Int -> IO ()
      go i | i < 0 = pure ()
      go i = do
        h <- hashCode ! i
        if h < 0 then
          go (i - 1)
        else do
          k <- key !~ i
          v <- value !~ i
          _ <- f k v
          go (i - 1)
  go (count - 1)
{-# INLINE forAssocs #-}

size :: MVector ks k => HashTable ks k vs v -> IO Int
size (HashTable h) = Data.Vector.Hashtables.size h
{-# INLINE size #-}

-- | Look up a key in the table. If it's already there, proceed with
--   the first @(v -> m a) argument. Otherwise run the @(m v) argument,
--   insert the result value in the table and pass it to the second @(v -> m a)
--   argument.
insertingIfAbsent :: forall ks k vs v a.
          (Hashable k, MVector ks k, MVector vs v)
       => HashTable ks k vs v
       -> k
       -> (v -> IO a)
       -> IO v
       -> (v -> IO a)
       -> IO a
insertingIfAbsent (HashTable DRef{..}) key' found getValue' notfound = do
    d@Dictionary{..} <- readMutVar getDRef
    let
        hashCode' = hash key' .&. mask
        !targetBucket = hashCode' `fastRem` remSize

        go :: Int -> IO a
        go i    | i >= 0 = do
                    hc <- hashCode ! i
                    if hc == hashCode'
                        then do
                            k  <- key !~ i
                            if k == key'
                                then do
                                  v <- value !~ i
                                  found v
                                else go =<< next ! i
                        else go =<< next ! i
                | otherwise = addOrResize

        addOrResize :: IO a
        addOrResize = do
            freeCount <- refs ! getFreeCount
            value' <- getValue'
            if freeCount > 0
                then do
                    index <- refs ! getFreeList
                    nxt <- next ! index
                    refs <~ getFreeList $ nxt
                    refs <~ getFreeCount $ freeCount - 1
                    add index targetBucket value'
                else do
                    count <- refs ! getCount
                    refs <~ getCount $ count + 1
                    nextLen <- A.getSizeofMutablePrimArray next
                    if count == nextLen
                        then do
                            nd <- resize d count hashCode' key' value'
                            writeMutVar getDRef nd
                            notfound value'
                        else add count targetBucket value'

        add :: Int -> Int -> v -> IO a
        add !index !targetBucket !value' = do
            hashCode <~ index $ hashCode'
            b <- buckets ! targetBucket
            next <~ index $ b
            key <~~ index $ key'
            value <~~ index $ value'
            buckets <~ targetBucket $ index
            notfound value'

    go =<< buckets ! targetBucket
{-# INLINE insertingIfAbsent #-}

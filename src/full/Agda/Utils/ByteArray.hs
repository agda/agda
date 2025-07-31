{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

-- | Utilities for working with 'ByteArray' and 'ByteArray#'.
module Agda.Utils.ByteArray
  (
  -- * Constructing byte arrays
    byteArrayOnes#
  -- * Queries
  , byteArrayIsSubsetOf#
  , byteArrayDisjoint#
  -- * Folds
  --
  -- $byteArrayFolds
  , byteArrayFoldrBits#
  , byteArrayFoldlBits#
  -- ** Strict folds
  , byteArrayFoldrBitsStrict#
  , byteArrayFoldlBitsStrict#
  ) where

-- We need the machines word size for some bitwise operations.
#include "MachDeps.h"

import GHC.Base
import GHC.Num.WordArray

import Agda.Utils.Word

--------------------------------------------------------------------------------
-- Constructing byte arrays

-- | Construct a 'ByteArray#' consisting of @n@ 1 bits.
byteArrayOnes# :: Int# -> ByteArray#
byteArrayOnes# n =
  let !(# q, r #) = quotRemInt# n WORD_SIZE_IN_BITS# in
  if isTrue# (r ==# 0#) then
    withNewWordArray# q \mwa st ->
      byteArrayFillOnes# mwa 0# q st
  else
    withNewWordArray# (q +# 1#) \mwa st ->
      let st' = byteArrayFillOnes# mwa 0# q st
      in mwaWrite# mwa q (uncheckedWordOnes# r) st'
{-# NOINLINE byteArrayOnes# #-}

-- | @byteArrayFillOnes# mwa start end st@ will fill a 'MutableByteArray#' with
-- ones from @start@ to @end - 1@.
byteArrayFillOnes# :: MutableByteArray# s -> Int# -> Int# -> State# s -> State# s
byteArrayFillOnes# bs i len st =
  if isTrue# (i <# len) then
    let st' = mwaWrite# bs i (not# 0##) st
    in byteArrayFillOnes# bs (i +# 1#) len st'
  else
    st

--------------------------------------------------------------------------------
-- Queries

-- | Check that if the set bits of a 'ByteArray#' are a subset
-- of another 'ByteArray#'.
byteArrayIsSubsetOf# :: ByteArray# -> ByteArray# -> Int#
byteArrayIsSubsetOf# bs1 bs2 =
  if isTrue# (len1 <=# len2) then
    loop 0#
  else
    0#
  where
    len1 = wordArraySize# bs1
    len2 = wordArraySize# bs2

    loop :: Int# -> Int#
    loop i =
      if isTrue# (i <# len1) then
        let w1 = indexWordArray# bs1 i
            w2 = indexWordArray# bs2 i
        in if isTrue# ((w1 `and#` w2) `eqWord#` w1) then
          loop (i +# 1#)
        else
          0#
      else
        1#
{-# NOINLINE byteArrayIsSubsetOf# #-}

-- | Check if two 'ByteArray#'s are bitwise disjoint.
byteArrayDisjoint# :: ByteArray# -> ByteArray# -> Int#
byteArrayDisjoint# bs1 bs2 =
  let len1 = wordArraySize# bs1
      len2 = wordArraySize# bs2
  in if isTrue# (len1 <=# len2) then
    loop 0# len1
  else
    loop 0# len2
  where
    loop :: Int# -> Int# -> Int#
    loop i len =
      if isTrue# (i <# len) then
        let w1 = indexWordArray# bs1 i
            w2 = indexWordArray# bs2 i
        in if (isTrue# (disjointWord# w1 w2)) then
          loop (i +# 1#) len
        else
          0#
      else
        1#
{-# NOINLINE byteArrayDisjoint# #-}

--------------------------------------------------------------------------------
-- Folds

-- $byteArrayFolds
-- As usual, there is an ambiguity in left/right folds for folding over the bits of a
-- 'ByteArray#'. We opt to use the convention where we treat the 0th bit as the "head" of
-- the 'ByteArray#', so a right fold like @byteArrayFoldrBits# f x 0b1011@ would give @f 0 (f 1 (f 3 x))@.

-- | Perform a lazy right fold over the bit indicies of a 'ByteArray#'.
byteArrayFoldrBits# :: (Int -> a -> a) -> a -> ByteArray# -> a
byteArrayFoldrBits# f a bs = loop 0#
  where
    len = wordArraySize# bs

    -- Not tail recursive.
    loop i =
      if isTrue# (i <# len) then
        wordFoldrBitsOffset# (WORD_SIZE_IN_BITS# *# i) f (loop (i +# 1#)) (indexWordArray# bs i)
      else
        a

-- | Perform a lazy left fold over the bit indicies of a 'ByteArray#'.
byteArrayFoldlBits# :: (a -> Int -> a) -> a -> ByteArray# -> a
byteArrayFoldlBits# f a bs = loop (wordArraySize# bs -# 1#)
  where
    -- Not tail recursive.
    loop i =
      if isTrue# (i >=# 0#) then
        wordFoldlBitsOffset# (WORD_SIZE_IN_BITS# *# i) f (loop (i -# 1#)) (indexWordArray# bs i)
      else
        a

-- | Perform a strict right fold over the bit indicies of a 'ByteArray#'.
byteArrayFoldrBitsStrict# :: (Int -> a -> a) -> a -> ByteArray# -> a
byteArrayFoldrBitsStrict# f a bs = loop (wordArraySize# bs -# 1#) a
  where
    -- Tail recursive.
    loop i !acc =
      if isTrue# (i >=# 0#) then
        loop (i -# 1#) (wordFoldrBitsOffsetStrict# (WORD_SIZE_IN_BITS# *# i) f acc (indexWordArray# bs i))
      else
        acc

-- | Perform a strict left fold over the bit indicies of a 'ByteArray#'.
byteArrayFoldlBitsStrict# :: (a -> Int -> a) -> a -> ByteArray# -> a
byteArrayFoldlBitsStrict# f a bs = loop 0# a
  where
    len = wordArraySize# bs

    -- Tail recursive.
    loop i !acc =
      if isTrue# (i <# len) then
        loop (i +# 1#) (wordFoldlBitsOffsetStrict# (WORD_SIZE_IN_BITS# *# i) f acc (indexWordArray# bs i))
      else
        acc

{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
-- | Utilities for working with 'Natural'.
module Agda.Utils.Natural
  (
  -- * Bitwise operations
    naturalCountTrailingZeros
  -- * Folds
  , naturalFoldrBits
  , naturalFoldlBits
  -- * Re-exports
  , module Natural
  ) where

-- We need the machines word size for some bitwise operations.
#include "MachDeps.h"

import GHC.Base
import GHC.Num.BigNat
import GHC.Num.Natural as Natural

import Agda.Utils.Word

--------------------------------------------------------------------------------
-- Bitwise Operations

-- | Count the number of zeros after the least-signifigant bit.
--
-- >>> naturalCountTrailingZeros 8
-- 3
naturalCountTrailingZeros :: Natural -> Int
naturalCountTrailingZeros (NS w) = I# $ word2Int# $ ctz# w
naturalCountTrailingZeros (NB bs) = I# $ loop 0#
  where
    loop :: Int# -> Int#
    loop i =
      -- We don't need to check if the index goes out of bounds, as we know that
      -- 0 always gets stored as an @NS@, so there must be *some* sewt bit.
      let w = indexWordArray# bs i in
      if isTrue# (eqWord# w 0##) then
        loop (i +# 1#)
      else
        WORD_SIZE_IN_BITS# *# i +# (word2Int# $ ctz# w)

--------------------------------------------------------------------------------
-- Folds

-- | Perform a right fold over the bits of a 'Natural'.
naturalFoldrBits :: (Int -> a -> a) -> a -> Natural -> a
naturalFoldrBits f a (NS w) = wordFoldrBitsOffset# 0# f a w
naturalFoldrBits f a (NB bs) = bigNatFoldrBits# f a bs

-- | Perform a right fold over the bits of a 'BigNat#'.
bigNatFoldrBits# :: (Int -> a -> a) -> a -> BigNat# -> a
bigNatFoldrBits# f a bs = loop (bigNatSize# bs -# 1#)
  where
    loop i =
      if isTrue# (i ==# 0#) then
        a
      else
        wordFoldrBitsOffset# (WORD_SIZE_IN_BITS# *# i) f (loop (i +# 1#)) (indexWordArray# bs i)

-- | Perform a left fold over the bits of a 'Natural'.
naturalFoldlBits :: (a -> Int -> a) -> a -> Natural -> a
naturalFoldlBits f a (NS w) = wordFoldlBitsOffset# 0# f a w
naturalFoldlBits f a (NB bs) = bigNatFoldlBits# f a bs

-- | Perform a left fold over the bits of a 'BigNat#'.
bigNatFoldlBits# :: (a -> Int -> a) -> a -> BigNat# -> a
bigNatFoldlBits# f a bs = loop 0#
  where
    len = bigNatSize# bs
    loop i =
      if isTrue# (i >=# len) then
        a
      else
        wordFoldlBitsOffset# (WORD_SIZE_IN_BITS# *# i) f (loop (i +# 1#)) (indexWordArray# bs i)

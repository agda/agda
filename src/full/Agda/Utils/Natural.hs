{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
-- | Utilities for working with 'Natural'.
module Agda.Utils.Natural
  (
  -- * Size
    naturalSizeWords
  -- * Bitwise operations
  , naturalCountTrailingZeros
  , naturalAndNot
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
import GHC.Num.Natural as Natural hiding (naturalAndNot)

import Agda.Utils.Word

--------------------------------------------------------------------------------
-- Size

-- | How many words does a 'Natural' occupy?
naturalSizeWords# :: Natural -> Int#
naturalSizeWords# (NS _) = 1#
naturalSizeWords# (NB bs) = bigNatSize# bs

-- | How many words does a 'Natural' occupy?
naturalSizeWords :: Natural -> Int
naturalSizeWords n = I# (naturalSizeWords# n)

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

-- | Perform a logical AND NOT of two natural numbers.
--
-- This works around the broken implementation of 'naturalAndNot'
-- in @ghc-bignum@: see <https://gitlab.haskell.org/ghc/ghc/-/merge_requests/14552>
naturalAndNot :: Natural -> Natural -> Natural
naturalAndNot (NS w1) (NS w2) = NS (w1 `andNot#` w2)
naturalAndNot (NS w1) (NB bs2) = NS (w1 `andNot#` (bigNatToWord# bs2))
naturalAndNot (NB bs1) (NS w2) = NB (bigNatAndNotWord# bs1 w2)
naturalAndNot (NB bs1) (NB bs2) = naturalFromBigNat# (bigNatAndNot bs1 bs2)

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
      if isTrue# (i <# 0#) then
        a
      else
        wordFoldrBitsOffset# (WORD_SIZE_IN_BITS# *# i) f (loop (i -# 1#)) (indexWordArray# bs i)

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

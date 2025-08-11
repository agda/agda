{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}

-- | Utilities for working with 'Word' and 'Word#'.
module Agda.Utils.Word
  ( -- * Bitwise operations
    uncheckedBitWord#
  , uncheckedClearBitWord#
  , uncheckedSetBitWord#
  , uncheckedTestBitWord#
  , highestBitWord#
  , lowestBitWord#
  , disjointWord#
  , andNot#
  , uncheckedWordOnes#
  -- * Folds
  --
  -- $wordFolds
  , wordFoldrBits#
  , wordFoldlBits#
  , wordFoldrBitsOffset#
  , wordFoldlBitsOffset#
  -- ** Strict folds
  , wordFoldrBitsStrict#
  , wordFoldlBitsStrict#
  , wordFoldrBitsOffsetStrict#
  , wordFoldlBitsOffsetStrict#
  ) where

-- We need the machines word size for some bitwise operations.
#include "MachDeps.h"

import GHC.Base

--------------------------------------------------------------------------------
-- Bitwise operations

-- | Create a 'Word#' with the @i@th bit set.
--
-- The result of 'uncheckedBitWord#' is undefined when @i@
-- is not in the range @[0..WORD_SIZE_IN_BITS]@.
uncheckedBitWord# :: Int# -> Word#
uncheckedBitWord# i = 1## `uncheckedShiftL#` i
{-# INLINE uncheckedBitWord# #-}

-- | Clear a single bit in an unboxed word.
--
-- The result of 'uncheckedClearBitWord#' is undefined when @i@
-- is not in the range @[0..WORD_SIZE_IN_BITS]@.
uncheckedClearBitWord# :: Word# -> Int# -> Word#
uncheckedClearBitWord# w i =
  -- This is somewhat suboptimal. On x86, the GHC native code generator will
  -- produce the following code with -O2:
  --
  -- > movl $1,%eax
  -- > movq %rsi,%rcx
  -- > shlq %cl,%rax
  -- > notq %rax
  -- > movq %r14,%rbx
  -- > andq %rax,%rbx
  -- > jmp *(%rbp)
  --
  -- Ideally, this should be a single @btr@ instruction (or @bic@ on arm), but
  -- GHC doesn't provide any builtins for this so this is the best we can do.
  w `and#` (not# (1## `uncheckedShiftL#` i))
{-# INLINE uncheckedClearBitWord# #-}

-- | Set a single bit in an unboxed word.
--
-- The result of 'uncheckedSetBitWord#' is undefined when @i@
-- is not in the range @[0..WORD_SIZE_IN_BITS]@.
uncheckedSetBitWord# :: Word# -> Int# -> Word#
uncheckedSetBitWord# w i =
  w `or#` (1## `uncheckedShiftL#` i)
{-# INLINE uncheckedSetBitWord# #-}

-- | Test a single bit in an unboxed word.
--
-- The result of 'uncheckedTestBitWord#' is undefined when @i@
-- is not in the range @[0..WORD_SIZE_IN_BITS]@.
uncheckedTestBitWord# :: Word# -> Int# -> Int#
uncheckedTestBitWord# w i =
  (w `and#` (1## `uncheckedShiftL#` i)) `neWord#` 0##
{-# INLINE uncheckedTestBitWord# #-}

-- | Get the bit-index of the highest set bit.
highestBitWord# :: Word# -> Word#
highestBitWord# w =
  -- Another bit of suboptimal code resulting in a lack of primops.
  -- If we compile with -O2 using the native code generator on an x86 machine,
  -- we get:
  --
  -- > bsr %r14,%rax
  -- > movl $127,%ebx
  -- > cmovne %rax,%rbx
  -- > xorq $63,%rbx
  -- > xorq $63,%rbx
  -- > jmp *(%rbp)
  --
  -- Note the double @xor@! This could be a single @bsr@ instruction.
  -- If we compile with @-mbmi2@ things are a bit better, but still wastes
  -- an instruction. However, this is the best we can do.
  clz# w `xor#` (WORD_SIZE_IN_BITS## `minusWord#` 1##)
{-# INLINE highestBitWord# #-}

-- | Get the bit-index of the lowest set bit.
lowestBitWord# :: Word# -> Word#
lowestBitWord# w = ctz# w
{-# INLINE lowestBitWord# #-}

-- | Take the bitwise AND of the first argument with the complement of the second.
andNot# :: Word# -> Word# -> Word#
andNot# w1 w2 =
  -- This should be a single @andn@ on x86 or @bic@ on aarch64,
  -- but the native code generator doesn't know about this.
  w1 `and#` not# w2
{-# INLINE andNot# #-}

-- | Are the bit representations of two words disjoint?
disjointWord# :: Word# -> Word# -> Int#
disjointWord# w1 w2 = ((w1 `and#` w2) `eqWord#` 0##)
{-# INLINE disjointWord# #-}

-- | Create a 'Word#' where the first @n@ bits are 1.
--
-- The result of 'uncheckedWordOnes#' is undefined when @i@
-- is not in the range @[0..WORD_SIZE_IN_BITS]@.
uncheckedWordOnes# :: Int# -> Word#
uncheckedWordOnes# n = not# 0## `uncheckedShiftRL#` (WORD_SIZE_IN_BITS# -# n)
{-# INLINE uncheckedWordOnes# #-}

--------------------------------------------------------------------------------
-- Folds

-- $wordFolds
-- As usual, there is an ambiguity in left/right folds for folding over the bits of a
-- 'Word#'. We opt to use the convention where we treat the 0th bit as the "head" of
-- a 'Word#', so a right fold like @wordFoldrBits# f x 0b1011@ would give @f 0 (f 1 (f 3 x))@.
--
-- We also provide hand-rolled versions of folds that offset the bit index by a static value:
-- this pattern comes up quite often when folding over 'ByteArray#' and the like. This can
-- save some allocations when compared to @wordFoldrBits# (\i acc -> f (i + offset) acc) a@.

-- | @wordFoldrBits# f a w@ performs a lazy right fold over the bits of @w@.
wordFoldrBits# :: (Int -> a -> a) -> a -> Word# -> a
wordFoldrBits# f a w
  | isTrue# (w `eqWord#` 0##) = a
  | otherwise =
    let i = word2Int# (lowestBitWord# w)
    in f (I# i) (wordFoldrBits# f a (uncheckedClearBitWord# w i))

-- | @wordFoldrBitsOffset# offset f a w@ performs a right fold over the bits of @w@,
-- with every bit index passed to @f@ offset by @offset@.
wordFoldrBitsOffset# :: Int# -> (Int -> a -> a) -> a -> Word# -> a
wordFoldrBitsOffset# offset f a w
  | isTrue# (w `eqWord#` 0##) = a
  | otherwise =
    let i = word2Int# (lowestBitWord# w)
    in f (I# (i +# offset)) (wordFoldrBitsOffset# offset f a (uncheckedClearBitWord# w i))

-- | @wordFoldlBits# f a w@ performs a lazy left fold over the bits of @w@.
wordFoldlBits# :: (a -> Int -> a) -> a -> Word# -> a
wordFoldlBits# f a w
  | isTrue# (w `eqWord#` 0##) = a
  | otherwise =
      let i = word2Int# (highestBitWord# w)
      in f (wordFoldlBits# f a (uncheckedClearBitWord# w i)) (I# i)

-- | @wordFoldlBitsOffset# offset f a w@ performs a lazy left fold over the bits of @w@,
-- with every bit index passed to @f@ offset by @offset@.
wordFoldlBitsOffset# :: Int# -> (a -> Int -> a) -> a -> Word# -> a
wordFoldlBitsOffset# offset f a w
  | isTrue# (w `eqWord#` 0##) = a
  | otherwise =
      let i = word2Int# (highestBitWord# w)
      in f (wordFoldlBitsOffset# offset f a (uncheckedClearBitWord# w i)) (I# (i +# offset))

-- | @wordFoldrBitsStrict# f a w@ performs a strict right fold over the bits of @w@.
wordFoldrBitsStrict# :: (Int -> a -> a) -> a -> Word# -> a
wordFoldrBitsStrict# f !a w
  | isTrue# (w `eqWord#` 0##) = a
  | otherwise =
    let i = word2Int# (highestBitWord# w)
    in wordFoldrBitsStrict# f (f (I# i) a) (uncheckedClearBitWord# w i)

-- | @wordFoldrBitsOffsetStrict# offset f a w@ performs a strict right fold over the bits of @w@,
-- with every bit index passed to @f@ offset by @offset@.
wordFoldrBitsOffsetStrict# :: Int# -> (Int -> a -> a) -> a -> Word# -> a
wordFoldrBitsOffsetStrict# offset f !a w
  | isTrue# (w `eqWord#` 0##) = a
  | otherwise =
    let i = word2Int# (highestBitWord# w)
    in wordFoldrBitsOffsetStrict# offset f (f (I# (i +# offset)) a) (uncheckedClearBitWord# w i)

-- | @wordFoldlBitsStrict# f a w@ performs a strict left fold over the bits of @w@.
wordFoldlBitsStrict# :: (a -> Int -> a) -> a -> Word# -> a
wordFoldlBitsStrict# f !a w
  | isTrue# (w `eqWord#` 0##) = a
  | otherwise =
    let i = word2Int# (lowestBitWord# w)
    in wordFoldlBitsStrict# f (f a (I# i)) (uncheckedClearBitWord# w i)

-- | @wordFoldrBitsOffsetStrict# offset f a w@ performs a strict right fold over the bits of @w@,
-- with every bit index passed to @f@ offset by @offset@.
wordFoldlBitsOffsetStrict# :: Int# -> (a -> Int -> a) -> a -> Word# -> a
wordFoldlBitsOffsetStrict# offset f !a w
  | isTrue# (w `eqWord#` 0##) = a
  | otherwise =
    let i = word2Int# (lowestBitWord# w)
    in wordFoldlBitsOffsetStrict# offset f (f a (I# (i +# offset))) (uncheckedClearBitWord# w i)

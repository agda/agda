{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}

-- | Utilities for working with 'Word' and 'Word#'.
module Agda.Utils.Word
  ( -- * Bitwise operations
    clearBitWord#
  , lowestSetBitWord#
    -- * Folds
  , wordFoldlBitsOffset#
  , wordFoldrBitsOffset#
  ) where

-- We need the machines word size for some bitwise operations.
#include "MachDeps.h"

import GHC.Base

--------------------------------------------------------------------------------
-- Bitwise operations

-- | Clear a single bit in an unboxed word.
clearBitWord# :: Word# -> Int# -> Word#
clearBitWord# w i =
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
{-# INLINE clearBitWord# #-}

-- | Get the bit-index of the lowest set bit.
lowestSetBitWord# :: Word# -> Word#
lowestSetBitWord# w =
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
{-# INLINE lowestSetBitWord# #-}

--------------------------------------------------------------------------------
-- Folds

-- | @wordFoldlBitsOffset# offset f a w@ performs a left fold over the bits of @w@,
-- with every bit index passed to @f@ offset by @offset@.
wordFoldlBitsOffset# :: Int# -> (a -> Int -> a) -> a -> Word# -> a
wordFoldlBitsOffset# offset f a w = go w
  where
    go w =
      if isTrue# (w `eqWord#` 0##) then
        a
      else
        let i = word2Int# $ ctz# w
        in f (go (clearBitWord# w i)) (I# $ i +# offset)

-- | @wordFoldrBitsOffset# offset f a w@ performs a right fold over the bits of @w@,
-- with every bit index passed to @f@ offset by @offset@.
wordFoldrBitsOffset# :: Int# -> (Int -> a -> a) -> a -> Word# -> a
wordFoldrBitsOffset# offset f a w = go w
  where
    go w =
      if isTrue# (w `eqWord#` 0##) then
        a
      else
        let i = word2Int# $ lowestSetBitWord# w
        in f (I# $ i +# offset) (go (clearBitWord# w i))

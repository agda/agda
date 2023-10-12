
{-# LANGUAGE
   AllowAmbiguousTypes
 , CPP
 , MagicHash
 , RankNTypes
 , ScopedTypeVariables
 , TypeApplications
 , TypeOperators
 , UnboxedTuples
 #-}

module Agda.Utils.PrimData.Flat (
    Flat(..)
  , size
  , toByteOffset
  , fromByteOffset
  , sizeP
  , toByteOffsetP
  , fromByteOffsetP
  ) where

{-|
A class for types which can be naturally represented as uniform-sized pointer-free values.
-}

import GHC.Exts
import GHC.Int
import GHC.Word
#include "MachDeps.h"

#if SIZEOF_HSWORD == 8
#define WORDSHIFT 3
#elif SIZEOF_HSWORD == 4
#define WORDSHIFT 2
#endif

class Flat a where

  -- | Size of values of type @a@.
  size# :: Proxy# a -> Int#

  -- | Convert an offset in terms of type elements to an offset in terms
  --   of bytes.
  toByteOffset# :: Proxy# a -> Int# -> Int#

  -- | Convert a byte offset to an offset in terms of values of the type.
  fromByteOffset# :: Proxy# a -> Int# -> Int#

  -- | Read a value from the array. The offset is in elements of type
  -- @a@ rather than in bytes.
  indexByteArray# :: ByteArray# -> Int# -> a

  -- | Read a value from the mutable array. The offset is in elements of type
  -- @a@ rather than in bytes.
  readByteArray# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, a #)

  -- | Write a value to the mutable array. The offset is in elements of type
  -- @a@ rather than in bytes.
  writeByteArray# :: MutableByteArray# s -> Int# -> a -> State# s -> State# s

  -- | Read a value from a memory position given by an address and an offset.
  -- The memory block the address refers to must be immutable. The offset is in
  -- elements of type @a@ rather than in bytes.
  indexOffAddr# :: Addr# -> Int# -> a

  -- | Read a value from a memory position given by an address and an offset.
  -- The offset is in elements of type @a@ rather than in bytes.
  readOffAddr# :: Addr# -> Int# -> State# s -> (# State# s, a #)

  -- | Write a value to a memory position given by an address and an offset.
  -- The offset is in elements of type @a@ rather than in bytes.
  writeOffAddr# :: Addr# -> Int# -> a -> State# s -> State# s

  -- | Read a value from an array. The offset is in bytes.
  indexWord8ArrayAs# :: ByteArray# -> Int# -> a

  -- | Read a value from a mutable array. The offset is in bytes.
  readWord8ArrayAs# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, a #)

  -- | Write a value to a bytearray. The offset is in bytes.
  writeWord8ArrayAs# :: MutableByteArray# s -> Int# -> a -> State# s -> State# s

size :: forall a. Flat a => Int
size = I# (size# @a proxy#)
{-# INLINE size #-}

toByteOffset :: forall a. Flat a => Int -> Int
toByteOffset (I# i) = I# (toByteOffset# @a proxy# i)
{-# INLINE toByteOffset #-}

fromByteOffset :: forall a. Flat a => Int -> Int
fromByteOffset (I# i) = I# (fromByteOffset# @a proxy# i)
{-# INLINE fromByteOffset #-}

sizeP :: forall a. Flat a => Proxy# a -> Int
sizeP _ = I# (size# @a proxy#)
{-# INLINE sizeP #-}

toByteOffsetP :: forall a. Flat a => Proxy# a -> Int -> Int
toByteOffsetP _ (I# i) = I# (toByteOffset# @a proxy# i)
{-# INLINE toByteOffsetP #-}

fromByteOffsetP :: forall a. Flat a => Proxy# a -> Int -> Int
fromByteOffsetP _ (I# i) = I# (fromByteOffset# @a proxy# i)
{-# INLINE fromByteOffsetP #-}

#define derivePrim(ty, ctr, sz, tobo, frombo, idx_arr, rd_arr, wr_arr, idx_addr, rd_addr, wr_addr, idx_as, read_as, write_as) \
instance Flat (ty) where {                                 \
  size# _ = sz                                             \
; toByteOffset# _ i = tobo                                 \
; fromByteOffset# _ i = frombo                             \
; indexByteArray# arr i = ctr (idx_arr arr i)              \
; readByteArray#  arr i s = case rd_arr arr i s of         \
                        { (# s1, x #) -> (# s1, ctr x #) } \
; writeByteArray# arr i (ctr x) s = wr_arr arr i x s       \
; indexOffAddr# addr i = ctr (idx_addr addr i)             \
; readOffAddr#  addr i s = case rd_addr addr i s of        \
                        { (# s1, x #) -> (# s1, ctr x #) } \
; writeOffAddr# addr i (ctr x) s = wr_addr addr i x s      \
; indexWord8ArrayAs# arr i  = ctr (idx_as arr i)           \
; readWord8ArrayAs# arr i s = case read_as arr i s of      \
                        { (# s1, x #) -> (# s, ctr x #) }  \
; writeWord8ArrayAs# arr i (ctr x) s = write_as arr i x s  \
; {-# INLINE size# #-}                                     \
; {-# INLINE toByteOffset# #-}                             \
; {-# INLINE fromByteOffset# #-}                           \
; {-# INLINE indexByteArray# #-}                           \
; {-# INLINE readByteArray# #-}                            \
; {-# INLINE writeByteArray# #-}                           \
; {-# INLINE indexOffAddr# #-}                             \
; {-# INLINE readOffAddr# #-}                              \
; {-# INLINE writeOffAddr# #-}                             \
; {-# INLINE indexWord8ArrayAs# #-}                        \
; {-# INLINE readWord8ArrayAs# #-}                         \
; {-# INLINE writeWord8ArrayAs# #-}                        \
}

derivePrim(Int, I#, SIZEOF_HSINT#,
           uncheckedIShiftL# i WORDSHIFT#,
           uncheckedIShiftRA# i WORDSHIFT#,
           indexIntArray#, readIntArray#, writeIntArray#,
           indexIntOffAddr#, readIntOffAddr#, writeIntOffAddr#,
           indexWord8ArrayAsInt#, readWord8ArrayAsInt#, writeWord8ArrayAsInt#)

derivePrim(Word, W#, SIZEOF_HSWORD#,
           uncheckedIShiftL# i WORDSHIFT#,
           uncheckedIShiftRA# i WORDSHIFT#,
           indexWordArray#, readWordArray#, writeWordArray#,
           indexWordOffAddr#, readWordOffAddr#, writeWordOffAddr#,
           indexWord8ArrayAsWord#, readWord8ArrayAsWord#, writeWord8ArrayAsWord#)

derivePrim(Double, D#, SIZEOF_HSDOUBLE#,
           uncheckedIShiftL# i 3#,
           uncheckedIShiftRA# i 3#,
           indexDoubleArray#, readDoubleArray#, writeDoubleArray#,
           indexDoubleOffAddr#, readDoubleOffAddr#, writeDoubleOffAddr#,
           indexWord8ArrayAsDouble#, readWord8ArrayAsDouble#, writeWord8ArrayAsDouble#)

derivePrim(Char, C#, SIZEOF_HSCHAR#,
           uncheckedIShiftL# i 2#,
           uncheckedIShiftRA# i 2#,
           indexWideCharArray#, readWideCharArray#, writeWideCharArray#,
           indexWideCharOffAddr#, readWideCharOffAddr#, writeWideCharOffAddr#,
           indexWord8ArrayAsWideChar#, readWord8ArrayAsWideChar#, writeWord8ArrayAsWideChar#)

derivePrim(Word8, W8#, SIZEOF_WORD8#,
           i,
           i,
           indexWord8Array#, readWord8Array#, writeWord8Array#,
           indexWord8OffAddr#, readWord8OffAddr#, writeWord8OffAddr#,
           indexWord8Array#, readWord8Array#, writeWord8Array#)

derivePrim(Word16, W16#, SIZEOF_WORD16#,
           uncheckedIShiftL# i 1#,
           uncheckedIShiftRA# i 1#,
           indexWord16Array#, readWord16Array#, writeWord16Array#,
           indexWord16OffAddr#, readWord16OffAddr#, writeWord16OffAddr#,
           indexWord8ArrayAsWord16#, readWord8ArrayAsWord16#, writeWord8ArrayAsWord16#)

derivePrim(Word32, W32#, SIZEOF_WORD32#,
           uncheckedIShiftL# i 2#,
           uncheckedIShiftRA# i 2#,
           indexWord32Array#, readWord32Array#, writeWord32Array#,
           indexWord32OffAddr#, readWord32OffAddr#, writeWord32OffAddr#,
           indexWord8ArrayAsWord32#, readWord8ArrayAsWord32#, writeWord8ArrayAsWord32#)

derivePrim(Word64, W64#, SIZEOF_WORD64#,
           uncheckedIShiftL# i 3#,
           uncheckedIShiftRA# i 3#,
           indexWord64Array#, readWord64Array#, writeWord64Array#,
           indexWord64OffAddr#, readWord64OffAddr#, writeWord64OffAddr#,
           indexWord8ArrayAsWord64#, readWord8ArrayAsWord64#, writeWord8ArrayAsWord64#)

derivePrim(Int8, I8#, SIZEOF_INT8#,
           i,
           i,
           indexInt8Array#, readInt8Array#, writeInt8Array#,
           indexInt8OffAddr#, readInt8OffAddr#, writeInt8OffAddr#,
           indexInt8Array#, readInt8Array#, writeInt8Array#)

derivePrim(Int16, I16#, SIZEOF_INT16#,
           uncheckedIShiftL# i 1#,
           uncheckedIShiftRA# i 1#,
           indexInt16Array#, readInt16Array#, writeInt16Array#,
           indexInt16OffAddr#, readInt16OffAddr#, writeInt16OffAddr#,
           indexWord8ArrayAsInt16#, readWord8ArrayAsInt16#, writeWord8ArrayAsInt16#)

derivePrim(Int32, I32#, SIZEOF_INT32#,
           uncheckedIShiftL# i 2#,
           uncheckedIShiftRA# i 2#,
           indexInt32Array#, readInt32Array#, writeInt32Array#,
           indexInt32OffAddr#, readInt32OffAddr#, writeInt32OffAddr#,
           indexWord8ArrayAsInt32#, readWord8ArrayAsInt32#, writeWord8ArrayAsInt32#)

derivePrim(Int64, I64#, SIZEOF_INT64#,
           uncheckedIShiftL# i 3#,
           uncheckedIShiftRA# i 3#,
           indexInt64Array#, readInt64Array#, writeInt64Array#,
           indexInt64OffAddr#, readInt64OffAddr#, writeInt64OffAddr#,
           indexWord8ArrayAsInt64#, readWord8ArrayAsInt64#, writeWord8ArrayAsInt64#)

derivePrim((Ptr a), Ptr, SIZEOF_HSPTR#,
           uncheckedIShiftL# i WORDSHIFT#,
           uncheckedIShiftRA# i WORDSHIFT#,
           indexAddrArray#, readAddrArray#, writeAddrArray#,
           indexAddrOffAddr#, readAddrOffAddr#, writeAddrOffAddr#,
           indexWord8ArrayAsAddr#, readWord8ArrayAsAddr#, writeWord8ArrayAsAddr#)

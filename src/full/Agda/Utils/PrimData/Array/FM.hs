
{-# LANGUAGE
  UnboxedTuples, TypeOperators, MagicHash, RankNTypes, PolyKinds,
  TypeApplications, ScopedTypeVariables, BangPatterns, BlockArguments,
  RoleAnnotations, TypeFamilies, AllowAmbiguousTypes #-}

{-|
Flat mutable arrays.
-}

module Agda.Utils.PrimData.Array.FM where

import GHC.Exts
import GHC.IO (IO(..))
import Data.Kind

import Agda.Utils.PrimData.Flat
import qualified Agda.Utils.PrimData.Array.FI as FI
import Agda.Utils.PrimData.Unlifted
import Agda.Utils.PrimData.Errors

type role Array representational
data Array (a :: Type) = Array (MutableByteArray# RealWorld)

elemType :: Array a -> Proxy# a
elemType _ = proxy#
{-# INLINE elemType #-}

instance Unlifted (Array a) where
  type Rep (Array a) = MutableByteArray# RealWorld
  to# (Array arr) = arr
  from#           = Array
  {-# INLINE to# #-}
  {-# INLINE from# #-}
  defaultElem = empty
  {-# INLINE defaultElem #-}

new :: forall a. Flat a => Int -> IO (Array a)
new (I# n) = IO \s -> case newByteArray# (toByteOffset# @a proxy# n) s of
    (# s, marr #) -> (# s, Array marr #)
{-# INLINE new #-}

pinnedNew :: forall a. Flat a => Int -> IO (Array a)
pinnedNew (I# n) = IO \s -> case newPinnedByteArray# (toByteOffset# @a proxy# n) s of
    (# s, marr #) -> (# s, Array marr #)
{-# INLINE pinnedNew #-}

isPinned :: Array a -> Bool
isPinned (Array arr) = isTrue# (isMutableByteArrayPinned# arr)
{-# INLINE isPinned #-}

contents :: forall r a (b :: TYPE r). Array a -> (Addr# -> b) -> b
contents (Array arr) cont = case isMutableByteArrayPinned# arr of
  1# -> runRW# \s -> keepAlive# arr s \s -> cont (mutableByteArrayContents# arr)
  _  -> unpinnedContents
{-# INLINE contents #-}

empty :: Array a
empty = Array (runRW# \s -> case newByteArray# 0# s of
  (# s, arr #) -> arr)
{-# noINLINE empty #-}

copy :: forall a. Flat a => Array a -> Int -> Array a -> Int -> Int -> IO ()
copy (Array arr) (I# i) (Array arr') (I# i') (I# len) = IO \s ->
  case copyMutableByteArray#
          arr  (toByteOffset# @a proxy# i)
          arr' (toByteOffset# @a proxy# i')
               (toByteOffset# @a proxy# len) s of
    s -> (# s, () #)
{-# INLINE copy #-}

read :: forall a. Flat a => Array a -> Int -> IO a
read (Array arr) (I# i) = IO (readByteArray# arr i)
{-# INLINE read #-}

write :: forall a. Flat a => Array a -> Int -> a -> IO ()
write (Array arr) (I# i) a = IO \s ->
  case writeByteArray# arr i a s of
    s -> (# s, () #)
{-# INLINE write #-}

modify :: forall a.  Flat a => Array a -> Int -> (a -> a) -> IO ()
modify (Array arr) (I# i) f = IO \s -> case readByteArray# arr i s of
  (# s, a #) -> let !v = f a in case writeByteArray# arr i v s of
    s -> (# s, () #)
{-# INLINE modify #-}

map' :: forall a. Flat a => (a -> a) -> Array a -> IO ()
map' f (Array arr) = IO \s ->
  let go arr i n s = case i ==# n of
        1# -> (# s, () #)
        _  -> case readWord8ArrayAs# arr i s of
          (# s, a #) -> case a of
            !a -> case f a of
              !a -> case writeWord8ArrayAs# arr i a s of
                 s -> go arr (i +# size# @a proxy#) n s
  in go arr 0# (sizeofMutableByteArray# arr) s
{-# INLINE map' #-}

for :: forall a. Flat a => Array a -> (a -> IO ()) -> IO ()
for (Array arr) f = IO \s ->
  let go arr i n s = case i ==# n of
        1# -> (# s, () #)
        _  -> case readWord8ArrayAs# arr i s of
          (# s, a #) -> case a of
            !a -> case f a of
              IO f -> case f s of
                (# s, _ #) -> go arr (i +# size# @a proxy#) n s
  in go arr 0# (sizeofMutableByteArray# arr) s
{-# INLINE for #-}

set :: forall a. Flat a => Array a -> a -> IO ()
set (Array arr) a = IO \s ->
  let go arr i n s = case i ==# n of
        1# -> (# s, () #)
        _  -> case writeWord8ArrayAs# arr i a s of
          s -> go arr (i +# size# @a proxy#) n s
  in go arr 0# (sizeofMutableByteArray# arr) s
{-# INLINE set #-}

size :: forall a. Flat a => Array a -> Int
size (Array arr) = I# (fromByteOffset# @a proxy# (sizeofMutableByteArray# arr))
{-# INLINE size #-}

thaw :: forall a. FI.Array a -> IO (Array a)
thaw (FI.Array arr) =
  let n = sizeofByteArray# arr
  in IO \s -> case newByteArray# n s of
       (# s, marr #) -> case copyByteArray# arr 0# marr 0# n s of
         s -> (# s, Array marr #)
{-# INLINE thaw #-}

unsafeFreeze :: Array a -> IO (FI.Array a)
unsafeFreeze (Array marr) = IO \s -> case unsafeFreezeByteArray# marr s of
  (# s, arr #) -> (# s, FI.Array arr #)
{-# INLINE unsafeFreeze #-}


{-# language
  UnboxedTuples, TypeOperators, MagicHash, RankNTypes,
  TypeApplications, ScopedTypeVariables, BangPatterns, BlockArguments,
  RoleAnnotations, TypeFamilies, AllowAmbiguousTypes #-}

{-| Lifted mutable arrays. -}

module Agda.Utils.PrimData.Array.LM where

import GHC.Exts
import GHC.IO (IO(..))

import Agda.Utils.PrimData.Unlifted
import qualified Agda.Utils.PrimData.Array.LI as LI
import Agda.Utils.PrimData.Errors

type role Array representational
data Array a = Array (MutableArray# RealWorld a)

elemType :: Array a -> Proxy# a
elemType _ = proxy#
{-# INLINE elemType #-}

instance Unlifted (Array a) where
  type Rep (Array a) = (MutableArray# RealWorld a)
  to# (Array arr) = arr
  from#           = Array
  {-# INLINE to# #-}
  {-# INLINE from# #-}
  defaultElem = empty
  {-# INLINE defaultElem #-}

new :: forall a.  Int -> a -> IO (Array a)
new (I# i) a = IO (\s -> case newArray# i a s of
    (# s, arr #) -> (# s, Array arr #))

empty :: Array a
empty = Array (runRW# \s -> case newArray# 0# undefElem s of
  (# s, arr #) -> arr)
{-# noINLINE empty #-}

read :: forall a.  Array a -> Int -> IO a
read (Array arr) (I# i) = IO (readArray# arr i)
{-# INLINE read #-}

write :: forall a.  Array a -> Int -> a -> IO ()
write (Array arr) (I# i) a = IO \s ->
  case writeArray# arr i a s of
    s -> (# s, () #)
{-# INLINE write #-}

modify :: forall a.  Array a -> Int -> (a -> a) -> IO ()
modify (Array arr) (I# i) f = IO \s -> case readArray# arr i s of
  (# s, a #) -> case writeArray# arr i (f a) s of
    s -> (# s, () #)
{-# INLINE modify #-}

map' :: forall a b. (a -> b) -> Array a -> IO ()
map' f (Array arr) = IO \s ->
  let go :: forall s. MutableArray# s a -> Int# -> Int# -> State# s -> (# State# s, () #)
      go arr i n s = case i ==# n of
        1# -> (# s, () #)
        _  -> case readArray# arr i s of
          (# s, a #) -> let !v = unsafeCoerce# (f a) in case writeArray# arr i v s of
            s -> go arr (i +# 1#) n s
  in go arr 0# (sizeofMutableArray# arr) s
{-# INLINE map' #-}

for :: forall a. Array a -> (a -> IO ()) -> IO ()
for (Array arr) f = IO \s ->
  let go arr i n s = case i ==# n of
        1# -> (# s, () #)
        _  -> case readArray# arr i s of
          (# s, a #) -> case f a of
            IO f -> case f s of
              (# s, _ #) -> go arr (i +# 1#) n s
  in go arr 0# (sizeofMutableArray# arr) s
{-# INLINE for #-}

set :: forall a. Array a -> a -> IO ()
set arr a = map' (\_ -> a) arr
{-# INLINE set #-}

modify' :: forall a.  Array a -> Int -> (a -> a) -> IO ()
modify' (Array arr) (I# i) f = IO \s -> case readArray# arr i s of
  (# s, a #) -> let !v = f a in case writeArray# arr i v s of
    s -> (# s, () #)
{-# INLINE modify' #-}

size :: Array a -> Int
size (Array arr) = I# (sizeofMutableArray# arr)
{-# INLINE size #-}

thawSlice :: LI.Array a -> Int -> Int -> IO (Array a)
thawSlice (LI.Array arr) (I# start) (I# len) = IO \s ->
  case thawArray# arr start len s of
    (# s, marr #) -> (# s, Array marr #)
{-# INLINE thawSlice #-}

thaw :: forall a. LI.Array a -> IO (Array a)
thaw arr = thawSlice arr 0 (LI.size arr)
{-# INLINE thaw #-}

copySlice :: forall a. Array a -> Int -> Array a -> Int -> Int -> IO ()
copySlice (Array src) (I# i) (Array dst) (I# j) (I# len) = IO \s ->
  case copyMutableArray# src i dst j len s of
    s -> (# s, () #)
{-# INLINE copySlice #-}

sizedThaw :: forall a. Int -> LI.Array a -> IO (Array a)
sizedThaw size arr = thawSlice arr 0 size
{-# INLINE sizedThaw #-}

unsafeFreeze :: Array a -> IO (LI.Array a)
unsafeFreeze (Array marr) = IO \s -> case unsafeFreezeArray# marr s of
  (# s, arr #) -> (# s, LI.Array arr #)
{-# INLINE unsafeFreeze #-}

freezeSlice :: Array a -> Int -> Int -> IO (LI.Array a)
freezeSlice (Array marr) (I# start) (I# len) = IO \s ->
  case freezeArray# marr start len s of
    (# s, arr #) -> (# s, (LI.Array arr) #)
{-# INLINE freezeSlice #-}

freeze :: Array a -> IO (LI.Array a)
freeze arr = freezeSlice arr 0 (size arr)
{-# INLINE freeze #-}

sizedFreeze :: Int -> Array a -> IO (LI.Array a)
sizedFreeze size arr = freezeSlice arr 0 size
{-# INLINE sizedFreeze #-}

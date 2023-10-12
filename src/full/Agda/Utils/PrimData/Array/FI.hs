
{-# language
  UnboxedTuples, TypeOperators, MagicHash, RankNTypes,
  TypeApplications, ScopedTypeVariables, BangPatterns, BlockArguments,
  RoleAnnotations, TypeFamilies, AllowAmbiguousTypes #-}

{-|
Flat immutable arrays.
-}

module Agda.Utils.PrimData.Array.FI where

import GHC.Exts
import Agda.Utils.PrimData.Flat
import Agda.Utils.PrimData.Unlifted

type role Array representational
data Array a = Array ByteArray#

elemType :: Array a -> Proxy# a
elemType _ = proxy#
{-# INLINE elemType #-}

instance Unlifted (Array a) where
  type Rep (Array a) = ByteArray#
  to# (Array arr) = arr
  from#           = Array
  {-# INLINE to# #-}
  {-# INLINE from# #-}
  defaultElem = empty
  {-# INLINE defaultElem #-}

instance Semigroup (Array a) where
  (<>) = append; {-# INLINE (<>) #-}

instance Monoid (Array a) where
  mempty = empty; {-# INLINE mempty #-}

instance (Flat a, Show a) => Show (Array a) where
  show = show . Agda.Utils.PrimData.Array.FI.foldr (:) []
  {-# INLINE show #-}

new# :: forall a. Flat a => Int# -> ByteArray#
new# n = runRW# \s -> case newByteArray# (toByteOffset# @a proxy# n) s of
    (# s, marr #) -> case unsafeFreezeByteArray# marr s of
      (# _, arr #) -> arr
{-# INLINE new# #-}

new :: forall a. Flat a => Int -> Array a
new (I# n) = Array (new# @a n)
{-# INLINE new #-}

empty :: Array a
empty = Array (runRW# \s -> case newByteArray# 0# s of
    (# s, marr #) -> case unsafeFreezeByteArray# marr s of
      (# _, arr #) -> arr)
{-# noINLINE empty #-}

cons :: forall a. Flat a => a -> Array a -> Array a
cons a (Array as) = runRW# \s ->
  let as_size = sizeofByteArray# as
      a_size  = Agda.Utils.PrimData.Flat.size# @a proxy#
  in case newByteArray# (as_size +# a_size) s of
    (# s, marr #) -> case writeByteArray# marr 0# a s of
      s -> case copyByteArray# as 0# marr a_size as_size s of
        s -> case unsafeFreezeByteArray# marr s of
          (# _, arr #) -> Array arr
{-# INLINE cons #-}

append :: Array a -> Array a -> Array a
append (Array a) (Array a') = runRW# \s ->
    let size_a  = sizeofByteArray# a in
    let size_a' = sizeofByteArray# a' in
    case newByteArray# (size_a +# sizeofByteArray# a') s of
      (# s, dst #) -> case copyByteArray# a 0# dst 0# size_a s of
        s -> case copyByteArray# a' 0# dst size_a size_a' s of
          s -> case unsafeFreezeByteArray# dst s of
            (# _, arr #) -> Array arr

infixl 7 !#
(!#) :: forall a. Flat a => ByteArray# -> Int# -> a
(!#) arr i = indexByteArray# @a arr i
{-# INLINE (!#) #-}

infixl 7 !
(!) :: forall a. Flat a => Array a -> Int -> a
(!) (Array arr) (I# i) = indexByteArray# @a arr i
{-# INLINE (!) #-}

indexByBytes :: forall a. Flat a => Array a -> Int -> a
indexByBytes (Array arr) (I# i) = indexWord8ArrayAs# @a arr i
{-# INLINE indexByBytes #-}

size# :: forall a. Flat a => ByteArray# -> Int#
size# arr = fromByteOffset# @a proxy# (sizeofByteArray# arr)
{-# INLINE size# #-}

size :: forall a. Flat a => Array a -> Int
size (Array arr) = I# (Agda.Utils.PrimData.Array.FI.size# @a arr)
{-# INLINE size #-}

sizeInBytes :: forall a. Flat a => Array a -> Int
sizeInBytes (Array arr) = I# (sizeofByteArray# arr)

sizedMap# :: forall a b. (Flat a, Flat b) => Int# -> (a -> b) -> ByteArray# -> ByteArray#
sizedMap# size f = \arr ->
    let go :: Int# -> MutableByteArray# s -> Int# -> State# s -> State# s
        go i marr size s = case i <# size of
            1# -> case writeByteArray# marr i (f ((!#) @a arr i)) s of
                s -> go (i +# 1#) marr size s
            _  -> s
    in runRW# \s ->
        case newByteArray# (toByteOffset# @b proxy# size) s of
            (# s, marr #) -> case go 0# marr size s of
                s -> case unsafeFreezeByteArray# marr s of
                  (# _, arr #) -> arr
{-# INLINE sizedMap# #-}

sizedMap :: forall a b. (Flat a, Flat b) => Int -> (a -> b) -> Array a -> Array b
sizedMap (I# s) f = \(Array arr) -> Array (sizedMap# s f arr)
{-# INLINE sizedMap #-}

map :: forall a b. (Flat a, Flat b) => (a -> b) -> Array a -> Array b
map f = \arr -> sizedMap @a @b (Agda.Utils.PrimData.Array.FI.size arr) f arr
{-# INLINE map #-}

foldr :: forall a b. Flat a => (a -> b -> b) -> b -> Array a -> b
foldr f = \z (Array arr) -> go 0# (Agda.Utils.PrimData.Array.FI.size# @a arr) z arr where
    go i s z arr = case i <# s of
        1# -> f (arr !# i :: a) (go (i +# 1#) s z arr)
        _  -> z
{-# INLINE foldr #-}

foldr' :: forall a b. Flat a => (a -> b -> b) -> b -> Array a -> b
foldr' f = \z (Array arr) -> go 0# (Agda.Utils.PrimData.Array.FI.size# @a arr) z arr where
    go i s z arr = case i <# s of
        1# -> let !a = arr !# i :: a; !b = go (i +# 1#) s z arr in f a b
        _  -> z
{-# INLINE foldr' #-}

rfoldr :: forall a b. Flat a => (a -> b -> b) -> b -> Array a -> b
rfoldr f = \z (Array arr) -> go (Agda.Utils.PrimData.Array.FI.size# @a arr -# 1#) z arr where
    go i z arr = case i >=# 0# of
        1# -> f (arr !# i :: a) (go (i -# 1#) z arr)
        _  -> z
{-# INLINE rfoldr #-}

rfoldr' :: forall a b. Flat a => (a -> b -> b) -> b -> Array a -> b
rfoldr' f = \z (Array arr) -> go (Agda.Utils.PrimData.Array.FI.size# @a arr -# 1#) z arr where
    go i z arr = case i >=# 0# of
        1# -> let !a = arr !# i :: a; !b = go (i -# 1#) z arr in f a b
        _  -> z
{-# INLINE rfoldr' #-}

foldl' :: forall a b. Flat a => (b -> a -> b) -> b -> Array a -> b
foldl' f = \z (Array arr) -> go 0# (Agda.Utils.PrimData.Array.FI.size# @a arr) z arr  where
    go i s !z arr = case i <# s of
        1# -> go (i +# 1#) s (f z (arr !# i :: a)) arr
        _  -> z
{-# INLINE foldl' #-}

rfoldl' :: forall a b. Flat a => (b -> a -> b) -> b -> Array a -> b
rfoldl' f = \z (Array arr) -> go (Agda.Utils.PrimData.Array.FI.size# @a arr -# 1#) z arr where
    go i !z arr = case i >=# 0# of
        1# -> go (i -# 1#) (f z (arr !# i :: a)) arr
        _  -> z
{-# INLINE rfoldl' #-}

fromList :: forall a. Flat a => [a] -> Array a
fromList xs = case length xs of
  I# len -> Array (runRW# \s ->
    case newByteArray# (toByteOffset# @a proxy# len) s of
      (# s, marr #) -> go xs 0# s where
        go (x:xs) i s = case Agda.Utils.PrimData.Flat.writeByteArray# marr i x s of
                          s -> go xs (i +# 1#) s
        go _      _ s = case unsafeFreezeByteArray# marr s of (# _, arr #) -> arr)
{-# INLINE fromList #-}

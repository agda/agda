
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UndecidableInstances #-}

module Agda.Utils.MinimalArray.Lifted where

import Data.Foldable qualified
import GHC.Exts
import GHC.Arr qualified as GHC
import Data.Primitive.Array qualified as A
import Control.Monad.Primitive

import Agda.Utils.Serialize
import Agda.Utils.Serialize qualified as Ser

newtype Array a = Array {unwrap :: A.Array a}
  deriving (Eq, Show, IsList, Functor, Foldable, Traversable)

{-# INLINE size #-}
size :: Array a -> Int
size (Array arr) = A.sizeofArray arr

{-# INLINE unsafeIndex #-}
unsafeIndex :: Array a -> Int -> a
unsafeIndex (Array arr) i = A.indexArray arr i

{-# INLINE index #-}
index :: Array a -> Int -> a
index arr i | 0 <= i && i < Agda.Utils.MinimalArray.Lifted.size arr =
  unsafeIndex arr i
index arr i = error "Array: out of bounds"

toList :: Array a -> [a]
toList = GHC.Exts.toList

fromList :: [a] -> Array a
fromList = GHC.Exts.fromList

fromListN :: Int -> [a] -> Array a
fromListN = GHC.Exts.fromListN

fromGHCArray :: GHC.Array i e -> Array e
fromGHCArray (GHC.Array _ _ _ arr) = Array (A.Array arr)

instance Serialize a => Serialize (Array a) where
  size = Data.Foldable.foldl' (\s a -> Ser.size a + s) (Ser.size (0::Int))

  put (Array (A.Array arr)) = Put \p s ->
    let go :: Addr# -> State# RealWorld -> Int#
              -> Int# -> Array# a -> (# Addr#, State# RealWorld #)
        go p s i sz arr = case i ==# sz of
          1# -> (# p, s #)
          _  -> case indexArray# arr i of
            (# a #) -> case unPut (put a) p s of
              (# p, s #) -> go p s (i +# 1#) sz arr
        sz = sizeofArray# arr
    in case unPut (put (I# sz)) p s of
      (# p, s #) -> go p s 0# sz arr

  get = do
    I# l <- get @Int
    Get \e p s ->
      let go :: Addr# -> Addr# -> State# RealWorld -> MutableArray# RealWorld a
                -> Int# -> Int# -> (# Addr#, State# RealWorld #)
          go e p s marr i l = case i ==# l of
            1# -> (# p, s #)
            _  -> case unGet (get @a) e p s of
              (# p, s, a #) -> case writeArray# marr i a s of
                s -> go e p s marr (i +# 1#) l
      in case newArray# l undefined s of
        (# s, marr #) -> case go e p s marr 0# l of
          (# p, s #) -> case unsafeFreezeArray# marr s of
            (# s, arr #) -> (# p, s, Array (A.Array arr) #)

-- | Strict traversal.
{-# INLINE traverseIO' #-}
traverseIO' :: (a -> IO b) -> Array a -> IO (Array b)
traverseIO' f (Array arr) = do
  !arr <- A.traverseArrayP f arr
  pure (Array arr)

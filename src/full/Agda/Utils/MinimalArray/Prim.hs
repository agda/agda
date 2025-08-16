{-# LANGUAGE GeneralizedNewtypeDeriving, UndecidableInstances #-}

module Agda.Utils.MinimalArray.Prim where

import GHC.Exts
import qualified Data.Primitive.PrimArray as A
import Data.Primitive.Types
import Control.Monad.Primitive

newtype Array a = Array {unwrap :: A.PrimArray a}
  deriving (Eq, Show, IsList)

{-# INLINE size #-}
size :: Prim a => Array a -> Int
size (Array arr) = A.sizeofPrimArray arr

{-# INLINE unsafeIndex #-}
unsafeIndex :: Prim a => Array a -> Int -> a
unsafeIndex (Array arr) i = A.indexPrimArray arr i

{-# INLINE index #-}
index :: Prim a => Array a -> Int -> a
index arr i | 0 <= i && i < size arr = unsafeIndex arr i
            | otherwise = error "Array: out of bounds"

{-# INLINE foldr' #-}
foldr' :: forall a b. Prim a => (a -> b -> b) -> b -> Array a -> b
foldr' f b (Array arr) = A.foldrPrimArray' f b arr

{-# INLINE foldl' #-}
foldl' :: forall a b. Prim a => (b -> a -> b) -> b -> Array a -> b
foldl' f b (Array arr) = A.foldlPrimArray' f b arr

{-# INLINE map #-}
map :: (Prim a, Prim b) => (Int -> a -> b) -> Array a -> Array b
map f (Array arr) = Array (A.imapPrimArray f arr)

toList :: Prim a => Array a -> [a]
toList = GHC.Exts.toList

fromList :: Prim a => [a] -> Array a
fromList = GHC.Exts.fromList

fromListN :: Prim a => Int -> [a] -> Array a
fromListN = GHC.Exts.fromListN

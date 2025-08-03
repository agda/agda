{-# LANGUAGE GeneralizedNewtypeDeriving, UndecidableInstances #-}

module Agda.Utils.MinimalArray.Lifted where

import GHC.Exts
import qualified Data.Primitive.Array as A
import Control.Monad.Primitive

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
index arr i | 0 <= i && i < size arr = unsafeIndex arr i
            | otherwise = error "Array: out of bounds"

toList :: Array a -> [a]
toList = GHC.Exts.toList

fromList :: [a] -> Array a
fromList = GHC.Exts.fromList

fromListN :: Int -> [a] -> Array a
fromListN = GHC.Exts.fromListN


module Agda.Utils.MinimalArray.MutableLifted where

import GHC.Arr qualified as GHC
import GHC.IOArray qualified as GHC
import Data.Coerce
import Data.Primitive.Array qualified as A
import Agda.Utils.MinimalArray.Lifted qualified as LA
import Control.Monad.Primitive

newtype Array s a = Array {unwrap :: A.MutableArray s a}
type IOArray a = Array RealWorld a

{-# INLINE new #-}
new :: forall a m. PrimMonad m => Int -> a -> m (Array (PrimState m) a)
new n arr = Array <$> A.newArray n arr

{-# INLINE size #-}
size :: Array s a -> Int
size (Array arr) = A.sizeofMutableArray arr

{-# INLINE unsafeRead #-}
unsafeRead :: PrimMonad m => Array (PrimState m) a -> Int -> m a
unsafeRead (Array arr) i = A.readArray arr i

{-# INLINE unsafeWrite #-}
unsafeWrite :: PrimMonad m => Array (PrimState m) a -> Int -> a -> m ()
unsafeWrite (Array arr) i a = A.writeArray arr i a

{-# INLINE read #-}
read :: PrimMonad m => Array (PrimState m) a -> Int -> m a
read arr i = do
  let s = size arr
  if 0 <= i && i < s then
    unsafeRead arr i
  else
    error "Array.read: out of bounds"

{-# INLINE write #-}
write :: PrimMonad m => Array (PrimState m) a -> Int -> a -> m ()
write arr i a = do
  let s = size arr
  if 0 <= i && i < s then
    unsafeWrite arr i a
  else
    error "Array.write: out of bounds"

{-# INLINE freeze #-}
freeze :: PrimMonad m => Array (PrimState m) a -> m (LA.Array a)
freeze (Array arr) = LA.Array <$> A.freezeArray arr 0 (size (Array arr))

{-# INLINE unsafeFreeze #-}
unsafeFreeze :: PrimMonad m => Array (PrimState m) a -> m (LA.Array a)
unsafeFreeze (Array arr) = LA.Array <$> A.unsafeFreezeArray arr

fromGHCArray :: GHC.IOArray i e -> IOArray e
fromGHCArray (GHC.IOArray (GHC.STArray _ _ _ arr)) =
  Array (A.MutableArray arr)

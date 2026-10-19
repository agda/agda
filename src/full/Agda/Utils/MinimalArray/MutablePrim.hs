
module Agda.Utils.MinimalArray.MutablePrim where

import Data.Coerce
import Data.Primitive.PrimArray qualified as A
import Agda.Utils.MinimalArray.Prim qualified as PA
import Control.Monad.Primitive
import Data.Primitive.Types

newtype Array s a = Array {unwrap :: A.MutablePrimArray s a}
type IOArray a = Array RealWorld a

{-# INLINE new #-}
new :: PrimMonad m => Prim a => Int -> m (Array (PrimState m) a)
new n = Array <$> A.newPrimArray n

{-# INLINE size #-}
size :: PrimMonad m => Prim a => Array (PrimState m) a -> m Int
size (Array arr) = A.getSizeofMutablePrimArray arr

{-# INLINE unsafeRead #-}
unsafeRead :: PrimMonad m => Prim a => Array (PrimState m) a -> Int -> m a
unsafeRead (Array arr) i = A.readPrimArray arr i

{-# INLINE unsafeWrite #-}
unsafeWrite :: PrimMonad m => Prim a => Array (PrimState m) a -> Int -> a -> m ()
unsafeWrite (Array arr) i a = A.writePrimArray arr i a

{-# INLINE read #-}
read :: PrimMonad m => Prim a => Array (PrimState m) a -> Int -> m a
read arr i = do
  s <- size arr
  if 0 <= i && i < s then
    unsafeRead arr i
  else
    error "Agda.Utils.MinimalArray.MutablePrim.read: out of bounds"

{-# INLINE write #-}
write :: PrimMonad m => Prim a => Array (PrimState m) a -> Int -> a -> m ()
write arr i a = do
  s <- size arr
  if 0 <= i && i < s then
    unsafeWrite arr i a
  else
    error "Agda.Utils.MinimalArray.MutablePrim.write: out of bounds"

{-# INLINE freeze #-}
freeze :: PrimMonad m => Prim a => Array (PrimState m) a -> m (PA.Array a)
freeze (Array arr) = do
  !s   <- size (Array arr)
  !arr <- A.freezePrimArray arr 0 s
  pure (PA.Array arr)

{-# INLINE set #-}
set :: PrimMonad m => Prim a => Array (PrimState m) a -> a -> m ()
set (Array arr) a = do
  s <- size (Array arr)
  A.setPrimArray arr 0 s a

{-# INLINE unsafeFreeze #-}
unsafeFreeze :: PrimMonad m => Array (PrimState m) a -> m (PA.Array a)
unsafeFreeze (Array arr) = PA.Array <$> A.unsafeFreezePrimArray arr

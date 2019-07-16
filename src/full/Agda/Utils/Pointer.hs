{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Agda.Utils.Pointer
  ( Ptr, newPtr, derefPtr, setPtr
  , updatePtr, updatePtrM
  ) where

import Control.DeepSeq
import Control.Concurrent.MVar

import Data.Function
import Data.Hashable
import Data.IORef

import System.IO.Unsafe

import Data.Data (Data (..))
import Data.Typeable (Typeable)

import Agda.Utils.Impossible

data Ptr a = Ptr { ptrTag :: !Integer
                 , ptrRef :: !(IORef a) }
  deriving Data

-- cheating because you shouldn't be digging this far anyway
instance Typeable a => Data (IORef a) where
  gunfold _ _ _ = __IMPOSSIBLE__
  toConstr      = __IMPOSSIBLE__
  dataTypeOf    = __IMPOSSIBLE__

{-# NOINLINE freshVar #-}
freshVar :: MVar Integer
freshVar = unsafePerformIO $ newMVar 0

fresh :: IO Integer
fresh = do
    x <- takeMVar freshVar
    putMVar freshVar $! x + 1
    return x

{-# NOINLINE newPtr #-}
newPtr :: a -> Ptr a
newPtr x = unsafePerformIO $ do
  i <- fresh
  Ptr i <$> newIORef x

derefPtr :: Ptr a -> a
derefPtr p = unsafePerformIO $ readIORef $ ptrRef p

{-# NOINLINE updatePtr #-}
updatePtr :: (a -> a) -> Ptr a -> Ptr a
updatePtr f p = unsafePerformIO $ p <$ modifyIORef (ptrRef p) f

setPtr :: a -> Ptr a -> Ptr a
setPtr !x = updatePtr (const x)

-- | If @f a@ contains many copies of @a@ they will all be the same pointer in
--   the result. If the function is well-behaved (i.e. preserves the implicit
--   equivalence, this shouldn't matter).
updatePtrM :: Functor f => (a -> f a) -> Ptr a -> f (Ptr a)
updatePtrM f p = flip setPtr p <$> f (derefPtr p)

instance Show a => Show (Ptr a) where
  show p = "#" ++ show (ptrTag p) ++ "{" ++ show (derefPtr p) ++ "}"

instance Functor Ptr where
  fmap f = newPtr . f . derefPtr

instance Foldable Ptr where
  foldMap f = f . derefPtr

instance Traversable Ptr where
  traverse f p = newPtr <$> f (derefPtr p)

instance Eq (Ptr a) where
  (==) = (==) `on` ptrTag

instance Ord (Ptr a) where
  compare = compare `on` ptrTag

instance Hashable (Ptr a) where
  hashWithSalt salt = (hashWithSalt salt) . ptrTag

instance NFData (Ptr a) where rnf x = seq x ()

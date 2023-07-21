
module Agda.Utils.Memo where

import Control.Monad.State
import System.IO.Unsafe
import Data.IORef
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HMap
import Data.Hashable

import Agda.Utils.Lens

-- Simple memoisation in a state monad

-- | Simple, non-reentrant memoisation.
memo :: MonadState s m => Lens' s (Maybe a) -> m a -> m a
memo tbl compute = do
  mv <- use tbl
  case mv of
    Just x  -> return x
    Nothing -> do
      x <- compute
      x <$ (tbl .= Just x)

-- | Recursive memoisation, second argument is the value you get
--   on recursive calls.
memoRec :: MonadState s m => Lens' s (Maybe a) -> a -> m a -> m a
memoRec tbl ih compute = do
  mv <- use tbl
  case mv of
    Just x  -> return x
    Nothing -> do
      tbl .= Just ih
      x <- compute
      x <$ (tbl .= Just x)

{-# NOINLINE memoUnsafe #-}
memoUnsafe :: Ord a => (a -> b) -> (a -> b)
memoUnsafe f = unsafePerformIO $ do
  tbl <- newIORef Map.empty
  return (unsafePerformIO . f' tbl)
  where
    f' tbl x = do
      m <- readIORef tbl
      case Map.lookup x m of
        Just y  -> return y
        Nothing -> do
          let y = f x
          writeIORef tbl (Map.insert x y m)
          return y

{-# NOINLINE memoUnsafeH #-}
memoUnsafeH :: (Eq a, Hashable a) => (a -> b) -> (a -> b)
memoUnsafeH f = unsafePerformIO $ do
  tbl <- newIORef HMap.empty
  return (unsafePerformIO . f' tbl)
  where
    f' tbl x = do
      m <- readIORef tbl
      case HMap.lookup x m of
        Just y  -> return y
        Nothing -> do
          let y = f x
          writeIORef tbl (HMap.insert x y m)
          return y


-- | Utilities for Data.IORef.

module Agda.Utils.IORef
  ( module Data.IORef
  , module Agda.Utils.IORef
  ) where

import Data.IORef

-- | Read 'IORef', modify it strictly, and return old value.
readModifyIORef' :: IORef a -> (a -> a) -> IO a
readModifyIORef' ref f = do
    x <- readIORef ref
    writeIORef ref $! f x
    return x

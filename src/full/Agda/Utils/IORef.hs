{-# LANGUAGE CPP #-}

-- | Provides @Data.IORef.modifyIORef'@ for @base < 4.6@.

module Agda.Utils.IORef
  ( module Data.IORef
  , module Agda.Utils.IORef
  ) where

import Data.IORef

#if !MIN_VERSION_base(4,6,0)

-- | Strict version of 'modifyIORef'.
--
-- /Since: 4.6.0.0/
modifyIORef' :: IORef a -> (a -> a) -> IO ()
modifyIORef' ref f = do
    x <- readIORef ref
    writeIORef ref $! f x

#endif

-- | Read 'IORef', modify it strictly, and return old value.
readModifyIORef' :: IORef a -> (a -> a) -> IO a
readModifyIORef' ref f = do
    x <- readIORef ref
    writeIORef ref $! f x
    return x

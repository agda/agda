{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Setup.LockFile ( withLockFile ) where

import           Control.Exception          ( IOException, finally, try )

import           System.Directory           ( removeFile )

#ifdef wasm32_HOST_ARCH
import           Control.Concurrent         ( threadDelay )

import           Data.Bits                  ( (.|.) )

import           System.Posix.Internals     ( c_open, c_close, o_CREAT, o_EXCL, o_WRONLY, withFilePath )
import           Foreign.C                  ( eEXIST, eINTR, getErrno, throwErrno )
#else
import           System.FileLock            ( pattern Exclusive, withFileLock )
#endif


-- | Run an action with an exclusive lock over the given path
withLockFile :: FilePath -> IO a -> IO a

#ifdef wasm32_HOST_ARCH
withLockFile path go =
  withFilePath path (worker baseDelay)
  -- Remove the lock file afterwards. Ignore any IOException (e.g. if the file
  -- does not exist).
  `finally` try @IOException (removeFile path)

  where
    baseDelay = 50000 -- 50ms
    maxDelay = 1000000 -- 1s

    -- Attempt to create our lock file, retrying until we succeed.
    worker delay cpath = do
      fd <- c_open cpath (o_CREAT .|. o_EXCL .|. o_WRONLY) 0o600
      if fd /= (-1) then c_close fd >> go
      else do
        error <- getErrno
        if error == eEXIST then threadDelay delay >> worker (min (delay * 2) maxDelay) cpath
        else if error == eINTR then worker delay cpath
        else throwErrno ("withLockFile: " ++ path)

#else
withLockFile path go =
  withFileLock path Exclusive (const go)
  -- Remove the lock (this is surprisingly not done by withFileLock).
  -- Ignore any IOException (e.g. if the file does not exist).
  `finally` try @IOException (removeFile path)
#endif

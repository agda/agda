{-# OPTIONS_GHC -Wunused-imports #-}

-- | Binary IO.

module Agda.Utils.IO.Binary
  ( readBinaryFile'
  ) where

import System.IO
import Data.ByteString.Lazy as BS

-- | Returns a close function for the file together with the contents.

readBinaryFile' :: FilePath -> IO (ByteString, IO ())
readBinaryFile' file = do
    h <- openBinaryFile file ReadMode
    s <- BS.hGetContents h
    return (s, hClose h)

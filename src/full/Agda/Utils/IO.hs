module Agda.Utils.IO
  ( readBinaryFile'
  ) where

import qualified System.IO.UTF8 as UTF8
import qualified System.IO as IO
import qualified Data.ByteString.Lazy as BS

-- | Returns a close function for the file together with the contents.

readBinaryFile' :: FilePath -> IO (BS.ByteString, IO ())
readBinaryFile' file = do
    h <- IO.openBinaryFile file IO.ReadMode
    s <- BS.hGetContents h
    return (s, IO.hClose h)

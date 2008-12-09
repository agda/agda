module Agda.Utils.IO
  ( readBinaryFile'
  , readTextFile
  , module System.IO.UTF8
  ) where

import System.IO.UTF8
import qualified System.IO.UTF8 as UTF8
import qualified System.IO as IO
import qualified Data.ByteString.Lazy as BS
import Control.Applicative

import Agda.Utils.Unicode

-- | Returns a close function for the file together with the contents.

readBinaryFile' :: FilePath -> IO (BS.ByteString, IO ())
readBinaryFile' file = do
    h <- IO.openBinaryFile file IO.ReadMode
    s <- BS.hGetContents h
    return (s, IO.hClose h)

-- | Reads a UTF8-encoded file in binary mode and converts all Unicode
-- line endings into '\n'.

readTextFile :: FilePath -> IO String
readTextFile file = convertLineEndings <$> UTF8.readFile file

module Agda.Utils.IO
  ( readBinaryFile'
  , readTextFile
  , module System.IO.UTF8
  ) where

import System.IO.UTF8
import qualified System.IO.UTF8 as UTF8
import qualified System.IO as IO
import qualified Data.ByteString.Lazy as BS
import Codec.Binary.UTF8.String (decode)
import Data.Char (ord)
import Control.Monad (liftM)

-- | Returns a close function for the file together with the contents.

readBinaryFile' :: FilePath -> IO (BS.ByteString, IO ())
readBinaryFile' file = do
    h <- IO.openBinaryFile file IO.ReadMode
    s <- BS.hGetContents h
    return (s, IO.hClose h)

-- | Reads a UTF8-encoded file in text mode.

readTextFile :: FilePath -> IO String
readTextFile n = liftM (decode . map (toEnum . ord)) (IO.readFile n)

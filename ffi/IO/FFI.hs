module IO.FFI where

import Control.Exception (bracketOnError)
import System.IO
  (openFile, IOMode(ReadMode), hClose, hFileSize, hGetContents)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

-- | A variant of IO with an extra dummy type parameter.

type AgdaIO a b = IO b

-- | Reads a finite file. Raises an exception if the file path refers
-- to a non-physical file (like @/dev/zero@).

readFiniteFile :: T.Text -> IO T.Text
readFiniteFile f = do
  h <- openFile (T.unpack f) ReadMode
  bracketOnError (return ()) (\_ -> hClose h) (\_ -> hFileSize h)
  TIO.hGetContents h

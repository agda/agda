module IO.FFI where

import Control.Exception (bracketOnError)
import System.IO
  (openFile, IOMode(ReadMode), hClose, hFileSize, hGetContents)

-- | A variant of IO with an extra dummy type parameter.

type AgdaIO a b = IO b

-- | Reads a finite file. Raises an exception if the file path refers
-- to a non-physical file (like @/dev/zero@).

readFiniteFile :: FilePath -> IO String
readFiniteFile f = do
  h <- openFile f ReadMode
  bracketOnError (return ()) (\_ -> hClose h) (\_ -> hFileSize h)
  hGetContents h

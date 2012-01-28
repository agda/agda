{-# LANGUAGE CPP #-}

-- | Text IO using the UTF8 character encoding.

module Agda.Utils.IO.UTF8
  ( readTextFile
  , Agda.Utils.IO.UTF8.hPutStr
  , Agda.Utils.IO.UTF8.writeFile
  , writeFileAndSync
  ) where

#if MIN_VERSION_base(4,2,0)
import qualified System.IO as IO
#else
import qualified System.IO.UTF8 as UTF8
#endif
import System.FilePath
#if defined(VERSION_unix)
import System.Posix.Fsync
import System.Posix.IO
#endif
import Control.Applicative
import Control.Exception

import Agda.Utils.Unicode

-- | Reads a UTF8-encoded text file and converts all Unicode line
-- endings into '\n'.

readTextFile :: FilePath -> IO String
readTextFile file = convertLineEndings <$> do
#if MIN_VERSION_base(4,2,0)
  h <- IO.openFile file IO.ReadMode
  IO.hSetNewlineMode h IO.noNewlineTranslation
  IO.hSetEncoding h IO.utf8
  IO.hGetContents h
#else
  UTF8.readFile file
#endif

-- | Writes UTF8-encoded text to the handle, which should be opened
-- for writing and in text mode. The native convention for line
-- endings is used.

hPutStr :: IO.Handle -> String -> IO ()
#if MIN_VERSION_base(4,2,0)
hPutStr h s = do
  IO.hSetEncoding h IO.utf8
  IO.hPutStr h s
#else
hPutStr = UTF8.hPutStr
#endif

-- | Writes a UTF8-encoded text file. The native convention for line
-- endings is used.

writeFile :: FilePath -> String -> IO ()
writeFile file s = IO.withFile file IO.WriteMode $ \h -> do
  hPutStr h s

-- | Writes the string to the file (like 'writeFile'), and, when done
-- writing, performs an @fsync@ on the file as well as its parent
-- directory (on certain platforms).

writeFileAndSync :: FilePath -> String -> IO ()
#if defined(VERSION_unix)
writeFileAndSync file s = do
  IO.withFile file IO.WriteMode $ \h -> do
    hPutStr h s
    fsync =<< handleToFd h
  bracket
     (openFd (takeDirectory file) ReadOnly Nothing defaultFileFlags)
     closeFd
     fsync
#else
writeFileAndSync = writeFile
#endif

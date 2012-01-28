{-# LANGUAGE CPP #-}

-- | Text IO using the UTF8 character encoding.

module Agda.Utils.IO.UTF8
  ( readTextFile
  , Agda.Utils.IO.UTF8.hPutStr
  , Agda.Utils.IO.UTF8.writeFile
  ) where

#if MIN_VERSION_base(4,2,0)
import qualified System.IO as IO
#else
import qualified System.IO.UTF8 as UTF8
#endif
import Control.Applicative

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
--
-- The handle's text encoding is not necessarily preserved, it is
-- changed to UTF8.

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
#if MIN_VERSION_base(4,2,0)
writeFile file s = IO.withFile file IO.WriteMode $ \h -> do
  hPutStr h s
#else
writeFile = UTF8.writeFile
#endif

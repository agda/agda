{-# OPTIONS_GHC -fwarn-missing-signatures #-}

-- | Text IO using the UTF8 character encoding.

module Agda.Utils.IO.UTF8
  ( readTextFile
  , Agda.Utils.IO.UTF8.hPutStr
  , Agda.Utils.IO.UTF8.writeFile
  ) where

import qualified System.IO as IO
import Control.Applicative

-- | Converts many character sequences which may be interpreted as
-- line or paragraph separators into '\n'.

convertLineEndings :: String -> String
convertLineEndings ('\x000D' : '\x000A' : s) = '\n' : convertLineEndings s
convertLineEndings ('\x000A'            : s) = '\n' : convertLineEndings s
convertLineEndings ('\x000D'            : s) = '\n' : convertLineEndings s
convertLineEndings ('\x0085'            : s) = '\n' : convertLineEndings s
convertLineEndings ('\x000C'            : s) = '\n' : convertLineEndings s
convertLineEndings ('\x2028'            : s) = '\n' : convertLineEndings s
convertLineEndings ('\x2029'            : s) = '\n' : convertLineEndings s
convertLineEndings (c                   : s) = c    : convertLineEndings s
convertLineEndings ""                        = ""

-- | Reads a UTF8-encoded text file and converts all Unicode line
-- endings into '\n'.

readTextFile :: FilePath -> IO String
readTextFile file = convertLineEndings <$> do
  h <- IO.openFile file IO.ReadMode
  IO.hSetNewlineMode h IO.noNewlineTranslation
  IO.hSetEncoding h IO.utf8
  IO.hGetContents h

-- | Writes UTF8-encoded text to the handle, which should be opened
-- for writing and in text mode. The native convention for line
-- endings is used.
--
-- The handle's text encoding is not necessarily preserved, it is
-- changed to UTF8.

hPutStr :: IO.Handle -> String -> IO ()
hPutStr h s = do
  IO.hSetEncoding h IO.utf8
  IO.hPutStr h s

-- | Writes a UTF8-encoded text file. The native convention for line
-- endings is used.

writeFile :: FilePath -> String -> IO ()
writeFile file s = IO.withFile file IO.WriteMode $ \h -> do
  hPutStr h s

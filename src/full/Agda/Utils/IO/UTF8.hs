-- | Text IO using the UTF8 character encoding.

module Agda.Utils.IO.UTF8
  ( readTextFile
  , Agda.Utils.IO.UTF8.hPutStr
  , Agda.Utils.IO.UTF8.writeFile
  , writeTextToFile
  ) where

import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.IO as T
import qualified System.IO as IO

-- | Converts many character sequences which may be interpreted as
-- line or paragraph separators into '\n'.
--
-- Note that '\r\n' is assumed to have already been converted to '\n'.

convertLineEndings :: Text -> Text
convertLineEndings = T.map convert
  where
  -- ASCII:
  convert '\x000D' = '\n'  -- CR  (Carriage return)
  convert '\x000C' = '\n'  -- FF  (Form feed)
  -- Unicode:
  convert '\x0085' = '\n'  -- NEXT LINE
  convert '\x2028' = '\n'  -- LINE SEPARATOR
  convert '\x2029' = '\n'  -- PARAGRAPH SEPARATOR
  -- Not a line ending (or '\x000A'):
  convert c        = c

-- | Reads a UTF8-encoded text file and converts many character
-- sequences which may be interpreted as line or paragraph separators
-- into '\n'.

readTextFile :: FilePath -> IO Text
readTextFile file = convertLineEndings <$> do
  h <- IO.openFile file IO.ReadMode
  IO.hSetNewlineMode h $
    IO.NewlineMode { IO.inputNL = IO.CRLF, IO.outputNL = IO.LF }
  IO.hSetEncoding h IO.utf8
  T.hGetContents h

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

-- | Writes a UTF8-encoded text file. The native convention for line
-- endings is used.

writeTextToFile :: FilePath -> Text -> IO ()
writeTextToFile file s = IO.withFile file IO.WriteMode $ \h -> do
  IO.hSetEncoding h IO.utf8
  T.hPutStr h s

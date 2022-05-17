-- | Text IO using the UTF8 character encoding.

module Agda.Utils.IO.UTF8
  ( readTextFile
  , Agda.Utils.IO.UTF8.readFile
  , Agda.Utils.IO.UTF8.writeFile
  , writeTextToFile
  ) where

import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.Encoding as T
import qualified Data.Text.Lazy.IO as T
import qualified Data.ByteString.Lazy as B
import qualified System.IO as IO
import qualified System.IO.Error as E

-- | Converts many character sequences which may be interpreted as
-- line or paragraph separators into '\n'.

convertLineEndings :: Text -> Text
convertLineEndings = T.map convert . convertNLCR
  where
  -- Replaces NL CR with NL.
  convertNLCR = T.replace "\n\x000D" "\n"

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
--
-- If the file cannot be decoded, then an 'IOException' is raised.

readTextFile :: FilePath -> IO Text
readTextFile file = do
  s <- T.decodeUtf8' <$> B.readFile file
  case s of
    Right s -> return $ convertLineEndings s
    Left _  -> E.ioError $ E.userError $
      "Failed to read the file " ++ file ++ ".\n" ++
      "Please ensure that this file uses the UTF-8 character encoding."

-- | Reads a UTF8-encoded text file and converts many character
-- sequences which may be interpreted as line or paragraph separators
-- into '\n'.

readFile :: FilePath -> IO String
readFile f = do
  s <- readTextFile f
  return $ T.unpack s

-- | Writes a UTF8-encoded text file. The native convention for line
-- endings is used.

writeFile :: FilePath -> String -> IO ()
writeFile file s = IO.withFile file IO.WriteMode $ \h -> do
  IO.hSetEncoding h IO.utf8
  IO.hPutStr h s

-- | Writes a UTF8-encoded text file. The native convention for line
-- endings is used.

writeTextToFile :: FilePath -> Text -> IO ()
writeTextToFile file s = IO.withFile file IO.WriteMode $ \h -> do
  IO.hSetEncoding h IO.utf8
  T.hPutStr h s

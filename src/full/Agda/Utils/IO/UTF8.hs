-- | Text IO using the UTF8 character encoding.

module Agda.Utils.IO.UTF8
  ( ReadException
  , readTextFile
  , Agda.Utils.IO.UTF8.readFile
  , Agda.Utils.IO.UTF8.writeFile
  , writeTextToFile
  ) where

import Control.Exception
import Data.Maybe (fromMaybe)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.Encoding as T
import qualified Data.Text.Lazy.IO as T
import qualified Data.ByteString.Lazy as BS
import qualified System.IO as IO

-- | Converts many character sequences which may be interpreted as
-- line or paragraph separators into '\n'.

convertLineEndings :: Text -> Text
convertLineEndings = T.map convert . convertCRLF
  where
  -- Replaces CR LF with LF.
  convertCRLF = T.replace "\x000D\n" "\n"

  -- ASCII:
  convert '\x000D' = '\n'  -- CR  (Carriage return)
  convert '\x000C' = '\n'  -- FF  (Form feed)
  -- Unicode:
  convert '\x0085' = '\n'  -- NEXT LINE
  convert '\x2028' = '\n'  -- LINE SEPARATOR
  convert '\x2029' = '\n'  -- PARAGRAPH SEPARATOR
  -- Not a line ending (or '\x000A'):
  convert c        = c

-- | Strip the byte order mark (BOM) from a Text.
--
-- - https://github.com/agda/agda/issues/6524
-- - https://github.com/haskell-hvr/cassava/issues/106#issuecomment-373986176
--
stripUtf8Bom :: BS.ByteString -> BS.ByteString
stripUtf8Bom bs = fromMaybe bs (BS.stripPrefix "\239\187\191" bs)

-- | A kind of exception that can be thrown by 'readTextFile' and
-- 'readFile'.
newtype ReadException
  = DecodingError FilePath
    -- ^ Decoding failed for the given file.
  deriving Show

instance Exception ReadException where
  displayException (DecodingError file) =
    "Failed to read " ++ file ++ ".\n" ++
    "Please ensure that this file uses the UTF-8 character encoding."

-- | Reads a UTF8-encoded text file and converts many character
-- sequences which may be interpreted as line or paragraph separators
-- into '\n'.
--
-- If the file cannot be decoded, then a 'ReadException' is raised.

readTextFile :: FilePath -> IO Text
readTextFile file = do
  s <- T.decodeUtf8' . stripUtf8Bom <$> BS.readFile file
  case s of
    Right s -> return $ convertLineEndings s
    Left _  -> throw $ DecodingError file

-- | Reads a UTF8-encoded text file and converts many character
-- sequences which may be interpreted as line or paragraph separators
-- into '\n'.
--
-- If the file cannot be decoded, then a 'ReadException' is raised.

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

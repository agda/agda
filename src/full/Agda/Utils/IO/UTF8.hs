{-# LANGUAGE CPP #-}

-- | Text IO using the UTF8 character encoding.

module Agda.Utils.IO.UTF8
  ( ReadException
  , readTextFile
  , readTextFileWithTime
  , Agda.Utils.IO.UTF8.readFile
  , Agda.Utils.IO.UTF8.writeFile
  , writeTextToFile
  ) where

import Control.Exception
import Control.Monad ((<$!>))
import Data.Maybe (fromMaybe)
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Data.Text.Lazy qualified as TL
import Data.Text.Lazy.IO qualified as TL
import Data.ByteString qualified as BS
import System.IO qualified as IO
import Data.Time.Clock (UTCTime)
import System.Directory (getModificationTime)

-- | Converts many character sequences which may be interpreted as
-- line or paragraph separators into '\n'.

convertLineEndings :: TL.Text -> TL.Text
convertLineEndings = TL.map convert . convertCRLF
  where
  -- Replaces CR LF with LF.
  convertCRLF = TL.replace "\x000D\n" "\n"

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
#if MIN_VERSION_base(4,20,0)
  backtraceDesired (DecodingError _) = False
#endif

readByteStringWithTime :: FilePath -> IO (BS.ByteString, UTCTime)
readByteStringWithTime file = do
  t <- getModificationTime file
  bstr <- BS.readFile file
  t' <- getModificationTime file
  if t /= t' then
    readByteStringWithTime file
  else pure (bstr, t)

-- | Reads a UTF8-encoded text file and converts many character
-- sequences which may be interpreted as line or paragraph separators
-- into '\n'. Also return the modification timestamp of the file.
--
-- If the file cannot be decoded, then a 'ReadException' is raised.
readTextFileWithTime :: FilePath -> IO (TL.Text, UTCTime)
readTextFileWithTime file = do
  (!bstr, !t) <- readByteStringWithTime file
  case T.decodeUtf8' $ stripUtf8Bom bstr of
    Right s -> do
      let !s' = convertLineEndings $! TL.fromStrict s
      pure (s', t)
    Left _ -> throw $ DecodingError file

readTextFile :: FilePath -> IO TL.Text
readTextFile file = fst <$!> readTextFileWithTime file

-- | Reads a UTF8-encoded text file and converts many character
-- sequences which may be interpreted as line or paragraph separators
-- into '\n'.
--
-- If the file cannot be decoded, then a 'ReadException' is raised.

readFile :: FilePath -> IO String
readFile f = do
  s <- readTextFile f
  return $ TL.unpack s

-- | Writes a UTF8-encoded text file. The native convention for line
-- endings is used.

writeFile :: FilePath -> String -> IO ()
writeFile file s = IO.withFile file IO.WriteMode $ \h -> do
  IO.hSetEncoding h IO.utf8
  IO.hPutStr h s

-- | Writes a UTF8-encoded text file. The native convention for line
-- endings is used.

writeTextToFile :: FilePath -> TL.Text -> IO ()
writeTextToFile file s = IO.withFile file IO.WriteMode $ \h -> do
  IO.hSetEncoding h IO.utf8
  TL.hPutStr h s

-- | Common syntax highlighting functions for Emacs and JSON

module Agda.Utils.IO.TempFile
  ( writeToTempFile
  ) where

import qualified Agda.Utils.IO.UTF8 as UTF8

import qualified Control.Exception as E
import qualified System.Directory as D
import qualified System.IO as IO

-- | Creates a temporary file, writes some stuff, and returns the filepath
writeToTempFile :: String -> IO FilePath
writeToTempFile content = do
  dir      <- D.getTemporaryDirectory
  E.bracket (IO.openTempFile dir "agda2-mode") (IO.hClose . snd) $ \ (filepath, handle) -> do
    UTF8.hPutStr handle content
    return filepath

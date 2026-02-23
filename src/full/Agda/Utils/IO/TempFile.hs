{-# OPTIONS_GHC -Wunused-imports #-}

-- | Common syntax highlighting functions for Emacs and JSON

module Agda.Utils.IO.TempFile
  ( writeToTempFile
  ) where

import Control.Exception qualified as E
import System.Directory qualified as D
import System.IO qualified as IO

-- | Creates a temporary file, writes some stuff, and returns the filepath
writeToTempFile :: String -> IO FilePath
writeToTempFile content = do
  dir      <- D.getTemporaryDirectory
  E.bracket (IO.openTempFile dir "agda2-mode") (IO.hClose . snd) $ \ (filepath, handle) -> do
    IO.hSetEncoding handle IO.utf8
    IO.hPutStr handle content
    return filepath

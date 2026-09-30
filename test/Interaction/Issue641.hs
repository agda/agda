-- This test tries to ensure that (certain) changes to OPTIONS pragmas
-- are respected when a file is reloaded.

{-# LANGUAGE RecordWildCards #-}

import Control.Monad
import System.Directory

import RunAgda

name          = "Issue641"
file          = name ++ ".agda"
interfaceFile = file ++ "i"
incorrectCode = "module " ++ name ++ " where\nFoo : Set\nFoo = Set\n"
correctCode   = "{-# OPTIONS --type-in-type #-}\n" ++ incorrectCode

main :: IO ()
main = runAgda ["--no-libraries"] $ \(AgdaCommands { .. }) -> do

  -- Discard the first prompt.
  echoUntilPrompt

  -- Edit the file.
  writeUTF8File file correctCode

  -- Load the file, and wait for Agda to complete.
  loadAndEcho file

  -- Remove the interface file.
  exists <- doesFileExist interfaceFile
  when exists $ removeFile interfaceFile

  -- Edit the file.
  writeUTF8File file incorrectCode

  -- Reload.
  loadAndEcho file

  return ()

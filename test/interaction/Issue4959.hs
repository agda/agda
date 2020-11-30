#!/usr/bin/env runhaskell

{-# LANGUAGE RecordWildCards #-}

import Data.List
import System.Directory
import System.Exit

import RunAgda

topLevel     = "Issue4959.agda"
importedName = "Issue4959-2"
imported     = importedName ++ ".agda"

main :: IO ()
main = runAgda [ "--no-libraries"
               , "--ignore-interfaces"
               ] $ \(AgdaCommands { .. }) -> do

  -- Discard the first prompt.
  echoUntilPrompt

  -- Set up and load the imported file.
  writeFile imported "-- 0"
  loadAndEcho imported

  -- Edit and load the imported file.
  writeFile imported "-- 1"
  loadAndEcho imported

  -- Load the top-level module.
  output <- loadAndEcho topLevel

  -- Clean up.
  removeFile imported

  -- Check the output.
  if ("Checking " ++ importedName) `isInfixOf` unlines output
  then exitFailure
  else exitSuccess

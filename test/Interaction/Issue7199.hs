#!/usr/bin/env runhaskell

{-# LANGUAGE RecordWildCards #-}

import Data.List
import System.Exit

import RunAgda

moduleM      = "module Issue7199.M where\n"
moduleMExtra = "postulate A : Set\n"

main :: IO ()
main = runAgda ["--no-libraries"] $ \(AgdaCommands { .. }) -> do

  -- Discard the first prompt.
  readUntilPrompt

  -- Make sure that Issue7199.M has been defined correctly.
  writeFile "Issue7199/M.agda" moduleM

  -- Load Issue7199. Discard the output.
  load "Issue7199.agda"
  readUntilPrompt

  -- Modify Issue7199.M.
  writeFile "Issue7199/M.agda" (moduleM ++ moduleMExtra)

  -- Load Issue7199.M in a separate process. Discard the output.
  (runAgda ["--no-libraries"] $ \(AgdaCommands { .. }) -> do
     readUntilPrompt
     load "Issue7199/M.agda"
     readUntilPrompt)

  -- Load Issue7199 again. Store the output.
  output <- loadAndEcho "Issue7199.agda"

  -- Restore Issue7199.M.
  writeFile "Issue7199/M.agda" moduleM

  -- Check the output.
  if not ("(agda2-status-action \"Checked\")" `elem` output)
  then do
    putStrLn "The file Issue7199 was not successfully type-checked."
    exitFailure
  else if any ("Checking Issue7199.M" `isInfixOf`) output
  then do
    putStrLn "The file Issue7199.M was rechecked."
    exitFailure
  else do
    putStrLn "The file Issue7199.M was not rechecked."
    exitSuccess

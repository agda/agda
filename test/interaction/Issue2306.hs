#!/usr/bin/env runhaskell

{-# LANGUAGE RecordWildCards #-}

import System.Directory

import RunAgda

file       = "Issue2306.agda"
firstCode  = unlines
               [ "B : Set"
               , "B = ?"
               ]
secondCode = unlines
               [ "A : Set"
               , "A = ?"
               ] ++
             firstCode

main :: IO ()
main = runAgda ["--no-libraries"]
         $ \(AgdaCommands { .. }) -> do

  -- Discard the first prompt.
  echoUntilPrompt

  -- Create the file.
  writeUTF8File file firstCode

  -- Load the file, and wait for Agda to complete.
  loadAndEcho file

  -- Edit the file.
  writeUTF8File file secondCode

  -- Check what the type of the goal is.
  send $
    command "goal_type" file (Just "Interactive Indirect")
            (Just "Normalised 0 noRange \"\"")

  -- Echo any output received from Agda.
  echoUntilPrompt

  return ()

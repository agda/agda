#!/usr/bin/env runhaskell

{-# LANGUAGE RecordWildCards #-}

import System.Directory

import RunAgda

file       = "Issue3082.agda"
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

  -- Compute token-based highlighting for the file.
  send $
    command "tokenHighlighting" file
            (Just "Interactive Indirect")
            (Just $ show file ++ " Keep")

  -- Echo any output received from Agda.
  echoUntilPrompt

  return ()

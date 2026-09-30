#!/usr/bin/env runhaskell

{-# LANGUAGE RecordWildCards #-}

import System.Directory

import RunAgda

file       = "Issue2728-3.agda"
firstCode  = unlines
               [ "{-# OPTIONS --safe #-}"
               , "module Issue2728-3 where"
               , "foo = Set -- something to cache"
               ]
secondCode = firstCode ++ "postulate B : Set\n"

main :: IO ()
main = runAgda [ "--no-libraries"
               , "--caching"
               ]
         $ \(AgdaCommands { .. }) -> do

  -- Discard the first prompt.
  echoUntilPrompt

  -- Create the file.
  writeUTF8File file firstCode

  -- Load the file, and wait for Agda to complete.
  loadAndEcho file

  -- Edit the file.
  writeUTF8File file secondCode

  -- Reload.
  loadAndEcho file

  return ()

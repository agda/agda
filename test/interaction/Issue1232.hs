{-# LANGUAGE RecordWildCards #-}

import System.Directory

import RunAgda

file       = "Issue1232.agda"
firstCode  = "import Issue1232.List"
secondCode = firstCode ++ "\n"

main :: IO ()
main = runAgda ["--caching"] $ \(AgdaCommands { .. }) -> do

  -- Check the library.
  callAgda ["Issue1232/All.agda", "--ignore-interfaces"]

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

  -- Clean up.
  writeUTF8File file "\n"
  removeFile $ file ++ "i"

  return ()

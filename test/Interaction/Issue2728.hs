{-# LANGUAGE RecordWildCards #-}

import Control.Exception

import RunAgda

file          = "Issue2728.agda"
correctCode   = "record R : Set where\n"
incorrectCode = correctCode ++ "  infix 0 _+_\n"

main :: IO ()
main = runAgda [ "--no-libraries"
               , "--caching"
               ] $ \(AgdaCommands { .. }) -> do

  -- Discard the first prompt.
  echoUntilPrompt

  -- Load the file, and wait for Agda to complete.
  loadAndEcho file

  bracket_
    -- Edit the file.
    (writeUTF8File file correctCode)

    -- Restore the original contents of the file.
    (writeUTF8File file incorrectCode)

    -- Reload.
    (loadAndEcho file)

  return ()

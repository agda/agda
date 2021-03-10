{-# LANGUAGE RecordWildCards #-}

import System.Directory
import System.Environment

import RunAgda

main :: IO ()
main = do
  -- For Unix-like systems.
  setEnv "TMPDIR" "/non-existent-directory-used-for-Issue4516"

  -- For Windows.
  setEnv "TMP" "/non-existent-directory-used-for-Issue4516"

  runAgda [ "--no-libraries"
          ] $ \(AgdaCommands { .. }) -> do

    -- Discard the first prompt.
    echoUntilPrompt

    -- Load the file, and wait for Agda to complete.
    loadAndEcho "Issue4516.agda"

    return ()

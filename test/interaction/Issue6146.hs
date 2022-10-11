-- An attempt to ensure that the correct .agda-lib file is used (or an
-- error message is presented) in the presence of symbolic links and
-- .. in paths.

{-# LANGUAGE RecordWildCards #-}

import Control.Exception
import Control.Monad
import System.Directory

import RunAgda

main :: IO ()
main = runAgda [ "--ignore-interfaces"
               , "--no-default-libraries"
               ] $ \(AgdaCommands { .. }) -> do

  -- Discard the first prompt.
  echoUntilPrompt

  -- Load a file, and wait for Agda to complete.
  loadAndEcho "Issue6146/A/B/../Issue6146.agda"

  -- Create a symbolic link (and remove it afterwards).
  bracket_
    (createDirectoryLink "B/C" "Issue6146/D")
    (removeDirectoryLink "Issue6146/D") $ do

    -- Load a file, and wait for Agda to complete.
    loadAndEcho "Issue6146/D/Issue6146.agda"

  -- Cleanup.
  exists <- doesDirectoryExist "Issue6146/_build"
  when exists $ removeDirectoryRecursive "Issue6146/_build"

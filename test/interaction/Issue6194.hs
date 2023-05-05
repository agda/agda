{-# LANGUAGE NondecreasingIndentation, RecordWildCards #-}

import Control.Exception

import System.Directory
import System.Process

import RunAgda

main :: IO ()
main = do
  -- Try to remove the MAlonzo directories and the binaries.
  let cleanup = do
        removePathForcibly "Issue6194-A/MAlonzo"
        removePathForcibly "Issue6194-A/Main"
        removePathForcibly "Issue6194-B/MAlonzo"
        removePathForcibly "Issue6194-B/Main"
  cleanup
  flip finally cleanup $ do

  -- Use Issue6194-A as the working directory.
  withCurrentDirectory "Issue6194-A" $ do

  runAgda [ "--no-libraries"
          , "--ignore-interfaces"
          ] $ \(AgdaCommands { .. }) -> do

  let
    -- Compile the given file and wait for Agda to complete.
    compile f = do
      send $ command "compile" f Nothing
               (Just $ "GHC " ++ show f ++ " []")
      readUntilPrompt

  -- Discard the first prompt.
  readUntilPrompt

  -- Compile Issue6194-A/Main.agda and wait for Agda to complete.
  compile "Main.agda"

  -- Compile Issue6194-B/Main.agda and wait for Agda to complete.
  compile "../Issue6194-B/Main.agda"

  -- Run Issue6194-B/Main.
  callProcess "../Issue6194-B/Main" []

  return ()

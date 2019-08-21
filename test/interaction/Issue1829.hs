{-# LANGUAGE RecordWildCards #-}

import Control.Monad

import RunAgda

file        = "Issue1829.agda"
extraArgs   = [ "--no-libraries"
              , "--caching"
              , "--ignore-interfaces"
              , "+RTS"
              , "-M5M"
              , "-RTS"
              ]
repetitions = 1000

-- Precondition: The program must be called with a single argument,
-- the path to Agda.

main :: IO ()
main = runAgda extraArgs $ \(AgdaCommands { .. }) -> do
  -- Run the given command repeatedly. Wait until the first
  -- command has completed before initiating the /third/ one. Why
  -- not the second one? Because this made the test case
  -- considerably slower.
  --
  -- Note that a prompt precedes the output from the first
  -- command. After the first command is initiated the initial
  -- prompt is discarded and then a second command is initiated.
  -- Only then is the output from the initial command echoed.
  replicateM_ repetitions $ loadAndEcho file

  -- Echo the final output.
  echoUntilPrompt

  return ()

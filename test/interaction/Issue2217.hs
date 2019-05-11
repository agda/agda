{-# LANGUAGE RecordWildCards #-}

import RunAgda

file = "Issue2217.agda"

-- A command that is intended to make Agda loop.
loop = command "give" file Nothing
         (Just "WithoutForce 0 noRange \"A\"")

-- One variant of the abort command.
abort = command "abort" file Nothing Nothing

main :: IO ()
main = runAgda [] $ \(AgdaCommands { .. }) -> do

  -- Discard the first prompt.
  echoUntilPrompt

  -- Abort all currently running commands. There are none, so
  -- (agda2-abort-done) is not sent to the front-end. No prompt is
  -- printed after an abort command.
  send abort

  -- Load the code.
  loadAndEcho file

  -- Invoke a looping command.
  send loop

  -- Abort all currently running commands.
  send abort

  -- A prompt is printed after the looping command has been aborted.
  echoUntilPrompt

  -- Load the file again. This and the following load commands should
  -- use the "decoded" interface for Issue2217.M, the interface should
  -- not be read from disk.
  loadAndEcho file

  -- Invoke a looping command twice.
  send loop
  send loop

  -- Abort all currently running commands.
  send abort

  -- A prompt is printed after the first looping command has been
  -- aborted. The second looping command is not started, so no prompt
  -- is printed for that command.
  echoUntilPrompt

  -- Load the file again.
  loadAndEcho file

  -- Invoke a looping command twice.
  send loop

  -- Abort all currently running commands, but not the next one (which
  -- might conceivably end up in the command queue before the looping
  -- command is aborted).
  send abort

  -- Load the file again.
  load file

  -- Now there should be two prompts, one for the aborted looping
  -- command and one for the load command.
  echoUntilPrompt
  echoUntilPrompt

  return ()

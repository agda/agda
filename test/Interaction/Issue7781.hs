{-# LANGUAGE RecordWildCards #-}

import Control.Exception (finally)

import RunAgda

file :: FilePath
file = "Issue7781.agda"

original, edited :: String
original = "opaque\n\n" ++ edited
edited = "-- XXXXXXXXXXXXXX\n"

-- Reproduce #7781: warning highlighting survives removing its cause and is
-- written to the interface, even though Agda no longer reports the warning.
-- The golden output records the current bug and needs updating when fixed.
main :: IO ()
main = flip finally (writeUTF8File file original) $ do
  writeUTF8File file original

  runAgda ["--no-default-libraries", "--ignore-interfaces", "-v0"] $
    \AgdaCommands { .. } -> do
      readUntilPrompt
      let reload = do
            send $ command "load" file (Just "NonInteractive Direct")
              (Just $ show file ++ " []")
            echoUntilPrompt

      putStrLn "Initial load:"
      reload

      writeUTF8File file edited
      putStrLn "After removing opaque:"
      reload
      putStrLn "Reload without further edits:"
      reload

      putStrLn "Stored highlighting:"
      send $ command "load_highlighting_info" file (Just "NonInteractive Direct")
        (Just $ show file)
      echoUntilPrompt
      return ()

  -- Start a fresh process without --ignore-interfaces to check the on-disk
  -- interface generated for the edited, warning-free source.
  runAgda ["--no-default-libraries", "-v0"] $ \AgdaCommands { .. } -> do
    readUntilPrompt
    putStrLn "Reload after restarting Agda:"
    send $ command "load" file (Just "NonInteractive Direct")
      (Just $ show file ++ " []")
    echoUntilPrompt
    return ()

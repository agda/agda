{-# LANGUAGE RecordWildCards #-}

import Control.Exception (finally)

import RunAgda

file :: FilePath
file = "Issue7781.agda"

original, edited :: String
original = "opaque\n\n" ++ edited
edited = "-- XXXXXXXXXXXXXX\n"

-- Regression test for #7781: removing the cause of a warning must remove its
-- highlighting as well, including from the interface loaded after a restart.
main :: IO ()
main = flip finally (writeUTF8File file original) $ do
  putStrLn "Empty opaque block:"
  reproduce original edited
  putStrLn "Missing definition:"
  reproduce "A : Set₁\n" "A : Set₁\nA = Set\n"

reproduce :: String -> String -> IO ()
reproduce before after = do
  writeUTF8File file before

  runAgda ["--no-default-libraries", "--ignore-interfaces", "-v0"] $
    \AgdaCommands { .. } -> do
      readUntilPrompt
      let reload = do
            send $ command "load" file (Just "NonInteractive Direct")
              (Just $ show file ++ " []")
            echoUntilPrompt

      putStrLn "Initial load:"
      reload

      writeUTF8File file after
      putStrLn "After fixing the warning:"
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

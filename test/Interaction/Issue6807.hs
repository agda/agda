{-# LANGUAGE RecordWildCards #-}

import RunAgda

file = "Issue6807.agda"

secondCode = unlines
  [ "opaque"
  , ""
  , "  A : Set₁"
  , "  A = Set"
  ]
firstCode = secondCode ++ unlines
  [ "B : Set₁"
  , "B = Set"
  ]

main :: IO ()
main = runAgda [ "--no-libraries"
               , "--caching"
               , "-vtc.decl:5"
               ] $ \(AgdaCommands { .. }) -> do

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
  writeUTF8File file ""

  return ()

{-# LANGUAGE RecordWildCards #-}

import Control.Exception

import RunAgda

file          = "Issue2728-2.agda"
firstPart s   = "F : {" ++ s ++ " : Set₁} → Set₁\nF {A} = A\n"
secondPart    = "G : Set₁\nG = F {A = Set}\n"
firstCode     = firstPart "_"
secondCode    = firstPart "_" ++ secondPart
thirdCode     = firstPart "A" ++ secondPart

main :: IO ()
main = runAgda [ "--no-libraries"
               , "--caching"
               ] $ \(AgdaCommands { .. }) -> do

  -- Discard the first prompt.
  echoUntilPrompt

  -- Load the file, and wait for Agda to complete.
  loadAndEcho file

  (do
    -- Edit the file and reload, twice.
    writeUTF8File file secondCode
    loadAndEcho file
    writeUTF8File file thirdCode
    loadAndEcho file)

    `finally`

    -- Restore the original contents of the file.
    writeUTF8File file firstCode

  return ()

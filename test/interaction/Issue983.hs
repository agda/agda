{-# LANGUAGE RecordWildCards #-}

import System.Directory

import RunAgda

top     = "Issue983"
topFile = top ++ ".agda"
lib     = top ++ "-Lib"
libFile = lib ++ ".agda"
badFile = top ++ "-Bad.agda"

main :: IO ()
main = runAgda [] $ \(AgdaCommands { .. }) -> do

  -- Discard the first prompt.
  echoUntilPrompt

  -- The library is empty.
  writeUTF8File libFile "\n"

  -- So this won't work.
  writeUTF8File badFile $ unlines
    [ "open import " ++ lib
    , "Bad = " ++ lib ++ ".NonExisting"
    ]

  -- Load the library.
  loadAndEcho libFile

  -- Now load top. This jumps to the error in bad.
  loadAndEcho topFile

  -- Load the highlighting info for bad. This looks in the
  -- moduleToSource map for lib, and this should not cause an internal
  -- error.
  send $ command "load_highlighting_info" badFile Nothing Nothing
  echoUntilPrompt

  -- Clean up.
  mapM_ removeFile [libFile, libFile ++ "i", badFile]

  return ()

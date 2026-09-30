{-# LANGUAGE RecordWildCards #-}

import Control.Monad
import System.Directory
import System.FilePath

import RunAgda

-- The directory used to store output created by this script. Will be
-- deleted.
name = "Issue2063"

mainFile = name </> "Bug.agda"

correctCode = unlines
  [ "module " ++ name ++ ".Bug where"
  , ""
  , "open import " ++ name ++ ".Class"
  ]
incorrectCode = correctCode ++ unlines
  [ "open import " ++ name ++ ".Instance"
  , "Rejected : Set"
  , "Rejected = A"
  ]

files =
  [ ( name </> "Class.agda"
    , unlines
        [ "module " ++ name ++ ".Class where"
        , ""
        , "record R : Set₁ where"
        , "  field"
        , "    A : Set"
        , ""
        , "open R ⦃ ... ⦄ public"
        ]
    )
  , ( name </> "Instance.agda"
    , unlines
        [ "module " ++ name ++ ".Instance where"
        , ""
        , "open import " ++ name ++ ".Class"
        , ""
        , "postulate"
        , "  instance"
        , "    i : R"
        ]
    )
  , ( mainFile
    , correctCode
    )
  ]

main :: IO ()
main = runAgda ["--no-libraries"] $ \(AgdaCommands { .. }) -> do
  -- Discard the first prompt.
  echoUntilPrompt

  -- Create some Agda files.
  exists <- doesDirectoryExist name
  when exists $ removeDirectoryRecursive name
  createDirectory name
  mapM_ (uncurry writeUTF8File) files

  -- Create some interface files.
  callAgda [name </> "Instance.agda"]

  -- Load the main module (with caching turned on), add some more
  -- lines of code, and reload the module.
  let loadBug = do
        send $ command "load" mainFile Nothing
                 (Just $ show mainFile ++ " " ++ show ["--caching"])
        echoUntilPrompt
  loadBug
  writeUTF8File mainFile incorrectCode
  loadBug

  removeDirectoryRecursive name

  return ()

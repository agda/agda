{-# LANGUAGE RecordWildCards #-}

import Control.Exception
import Data.List
import System.Exit

import RunAgda

issue8134_2 =
  unlines
    [ "{-# OPTIONS -vtc.decl:5 #-}"
    , "module Issue8134 (M : Set) where"
    , "open import Issue8134.M M"
    , "Should-not-be-rechecked : Set₁"
    , "Should-not-be-rechecked = Set"
    ]

issue8134_1 =
  issue8134_2 ++
  unlines
    [ "F : A → Set₁"
    , "F _ = Set"
    ]

main :: IO ()
main =
  runAgda [ "--no-default-libraries"
          , "--ignore-interfaces"
          ] $ \(AgdaCommands { .. }) -> do

  echoUntilPrompt

  -- Restore Issue8134.agda before exiting the script.
  flip finally (writeFile "Issue8134.agda" issue8134_1) $ do

    -- Write and load Issue8134.
    writeFile "Issue8134.agda" issue8134_1
    loadAndEcho "Issue8134.agda"

    -- Remove the last definition from Issue8134 and type-check the
    -- file again.
    writeFile "Issue8134.agda" issue8134_2
    ss1 <- loadAndEcho "Issue8134.agda"

    -- Restore the last definition and type-check the file one more
    -- time.
    writeFile "Issue8134.agda" issue8134_1
    ss2 <- loadAndEcho "Issue8134.agda"

    -- The definition "Should-not-be-rechecked" should not be
    -- rechecked.
    if any ("Checking Should-not-be-rechecked" `isInfixOf`) (ss1 ++ ss2)
      then exitFailure
      else return ()

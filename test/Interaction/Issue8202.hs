{-# LANGUAGE RecordWildCards #-}

import Control.Exception
import Control.Monad
import Data.List
import System.Directory
import System.Exit

import RunAgda

issue8202Base =
  unlines
    [ "open import Issue8202.M1"
    , "import Issue8202.M2"
    , "module Issue8202 (_ : Set) (open Issue8202.M2 Set) (r : R) where"
    , "postulate _ : R.A r"
    , "_ : Set₁"
    ]

issue8202_1 =
  issue8202Base ++
  unlines
    [ "_ = ?"
    ]

issue8202_2 =
  issue8202Base ++
  unlines
    [ "_ = Set"
    ]

main :: IO ()
main =
  runAgda [ "--no-default-libraries"
          , "--ignore-interfaces"
          ] $ \(AgdaCommands { .. }) -> do

  echoUntilPrompt

  -- Restore Issue8202.agda before exiting the script.
  flip finally (writeFile "Issue8202.agda" issue8202_1) $ do

    -- Load Issue8202.
    loadAndEcho "Issue8202.agda"

    -- Complete the final definition in Issue8202 and reload.
    writeFile "Issue8202.agda" issue8202_2
    ss <- loadAndEcho "Issue8202.agda"

    -- No internal error should be raised.
    if any ("__IMPOSSIBLE__" `isInfixOf`) ss
      then exitFailure
      else return ()

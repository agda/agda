{-# LANGUAGE RecordWildCards #-}

import Control.Monad

import System.FilePath
import System.Process
import System.Exit

import RunAgda

-- Make sure to typecheck N0 and N1 independently.
-- This is a workaround to issue #4272.
-- Upon proper handling of that issue, this test case
-- can be moved to test/Succeed (with N as main file).
modules =
  [ ("M", ExitSuccess)
  , ("N0", ExitSuccess)
  , ("N1", ExitSuccess)
  , ("N", ExitFailure undefined)
  ]

callAgdaWithExitCode :: [String] -> IO ExitCode
callAgdaWithExitCode agdaArgs = do
  agda <- getAgda
  withCreateProcess (proc agda agdaArgs) $ \_ _ _ -> waitForProcess

main :: IO ()
main = void $ do
  forM modules $ \(m, r) -> do
    r' <- callAgdaWithExitCode [ "--no-libraries" , "Issue4333" </> m <.> "agda" ]
    let isSuccess = (== ExitSuccess)
    when (isSuccess r /= isSuccess r') $ exitFailure

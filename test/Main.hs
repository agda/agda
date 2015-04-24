{-# LANGUAGE CPP #-} -- GHC 7.4.2 requires this indentation. See Issue 1460.
{-# LANGUAGE DoAndIfThenElse      #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main where

import qualified Exec.Tests as EXEC
import Test.Tasty
import Test.Tasty.Silver.Interactive as TM

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ((<$>))
#endif

import System.Environment
import System.Exit

main :: IO ()
main = do
  env <- getEnvironment
  case "AGDA_TESTS_PROPERLY_SETUP" `lookup` env of
    Just _ -> tests >>= TM.defaultMain
    Nothing -> do
        putStrLn $ unlines
            [ "The AGDA_TESTS_PROPERLY_SETUP environment variable is not set. Do not execute"
            , "these tests directly using \"cabal test\" or \"cabal install --run-tests\", instead"
            , "use the Makefile."
            , "Are you maybe using the Makefile together with an old cabal version?"
            , "Versions of cabal before 1.20.0.0 have a bug and will trigger this error. The Makefile"
            , "requries cabal 1.20.0.0 or later to work properly."
            , "See also Issue 1489 and 1490."
            ]
        exitWith (ExitFailure 1)

tests :: IO TestTree
tests = testGroup "all" <$> sequence [EXEC.tests]


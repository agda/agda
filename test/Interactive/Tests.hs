{-# LANGUAGE DoAndIfThenElse   #-}

module Interactive.Tests where

import qualified Data.Text.IO as TIO

import Test.Tasty
import Test.Tasty.HUnit
import System.FilePath
import System.Exit

import Utils

testDir :: FilePath
testDir = "test" </> "Interactive"

tests :: TestTree
tests = testGroup "Interactive"
  [ testCase "Naked" $ do
    runAgda [] "Naked"
  , testCase "Issue1430" $ do
    runAgda ["--no-libraries"] "Issue1430"
  ]
  where
    agdaArgs = [ "-I", "-i.", "-i..", "--ignore-interfaces" ]
    runAgda :: [String] -> FilePath -> IO ()
    runAgda extraArgs testName = do
      inp <- TIO.readFile (testDir </> testName <.> "in")
      ret@(c, _, _) <- readAgdaProcessWithExitCode (agdaArgs ++ extraArgs ++ [testDir </> testName <.> "agda"]) inp
      assertBool ("Agda returned error code: " ++ show ret) (c == ExitSuccess)

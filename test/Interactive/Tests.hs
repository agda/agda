module Interactive.Tests where

import Data.Foldable
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO

import Test.Tasty
import Test.Tasty.HUnit
import System.Directory
import System.FilePath
import System.Exit

import Agda.Utils.Monad
import Utils

testDir :: FilePath
testDir = "test" </> "Interactive"

tests :: TestTree
tests = testGroup "Interactive"
  [ testCase "Naked" $ do
    runAgda [testDir </> "Naked.agda"] "Naked"
  , testCase "Issue1430" $ do
    runAgda ["--no-libraries", testDir </> "Issue1430.agda"] "Issue1430"
  , testCase "Load" $ do
    runAgda ["--no-libraries"] "Load"
  ]
  where
    agdaArgs = [ "-I", "-i.", "-i..", "-itest/Interactive", "--ignore-interfaces" ]
    runAgda :: [String] -> FilePath -> IO ()
    runAgda extraArgs testName = do
      inp <- TIO.readFile (testDir </> testName <.> "in")
      ret@(c, stdout, stderr) <- readAgdaProcessWithExitCode (agdaArgs ++ extraArgs) inp
      assertBool ("Agda returned error code: " ++ show ret) (c == ExitSuccess)
      let stdoutFp = testDir </> testName <.> "stdout" <.> "expected"
          stderrFp = testDir </> testName <.> "stderr" <.> "expected"

      -- Check that every line in testName.stdout.expected (if exists) is a substring of stdout. Same for stderr.
      whenM (doesFileExist $ testDir </> testName <.> "stdout" <.> "expected") $ do
        expected <- TIO.readFile stdoutFp
        for_ (Text.lines expected) $
          assertBool ("Invalid stdout: " ++ show stdout) . (`Text.isInfixOf` stdout)
      whenM (doesFileExist $ testDir </> testName <.> "stderr" <.> "expected") $ do
        expected <- TIO.readFile stderrFp
        for_ (Text.lines expected) $
          assertBool ("Invalid stderr: " ++ show stderr) . (`Text.isInfixOf` stderr)

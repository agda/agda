module Interactive.Tests ( tests ) where

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
import Test.Tasty.Silver.Filter (RegexFilter (RFInclude))

testDir :: FilePath
testDir = "test" </> "Interactive"

tests :: TestTree
tests = testGroup "Interactive"
  [ fileTest "Issue1430"
  , bareTest "Naked"
  , bareTest "Load"
  ]
  where
    bareTest name = testCase name $ runAgda ["--no-libraries"] name
    fileTest name = testCase name $ runAgda ["--no-libraries", testDir </> name <.> "agda" ] name

agdaArgs :: [String]
agdaArgs = [ "-I", "-i.", "-i..", "-itest/Interactive", "--ignore-interfaces" ]

runAgda :: [String] -> FilePath -> IO ()
runAgda extraArgs testName = do
  inp <- TIO.readFile (testDir </> testName <.> "in")
  ret@(c, stdout, stderr) <- readAgdaProcessWithExitCode Nothing (agdaArgs ++ extraArgs) inp
  assertBool ("Agda returned error code: " ++ show ret) (c == ExitSuccess)
  let stdoutFp = testDir </> testName <.> "stdout" <.> "expected"
      stderrFp = testDir </> testName <.> "stderr" <.> "expected"
  checkOutput ("Invalid stdout: " ++ show stdout) stdout stdoutFp
  checkOutput ("Invalid stderr: " ++ show stderr) stderr stderrFp

checkOutput :: String -> Text -> FilePath -> IO ()
checkOutput msg output goldenFile = do
  whenM (doesFileExist goldenFile) do
    expected <- TIO.readFile goldenFile
    -- assertEqual msg expected output -- Does not work as agda -I prints repl stuff.
    -- Check that every line in testName.stdout.expected (if exists) is a substring of stdout. Same for stderr.
    forM_ (Text.lines expected) $
      assertBool msg . (`Text.isInfixOf` output)

{-# LANGUAGE MultiWayIf #-}

module Bugs.Tests where

import Data.Function (on)
import Data.Monoid ((<>))
import qualified Data.Text as T
import Data.Text.Encoding

import Test.Tasty
import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced
       (readFileMaybe, GDiff(..), GShow(..), goldenTest1)

import System.Directory
import System.Exit
import System.FilePath

import Utils

testDir :: FilePath
testDir = "test" </> "Bugs"

tests :: IO TestTree
tests = do
  inpFiles <- getAgdaFilesInDir NonRec testDir
  return $ testGroup "Bugs" $ map mkTest inpFiles

data TestResult
  = TestFailure T.Text
  | TestWarning T.Text
  | TestSuccess

mkTest :: FilePath -- ^ Agda file to test.
       -> TestTree
mkTest agdaFile =
  goldenTest1
    testName
    readGolden
    doRun
    (textDiff `on` printTestResult)
    (ShowText . printTestResult)
    resUpdate
  where
  testName   = asTestName testDir agdaFile
  flagFile   = dropAgdaExtension agdaFile <.> ".flags"
  errFile    = dropAgdaExtension agdaFile <.> ".err"
  warnFile   = dropAgdaExtension agdaFile <.> ".warn"

  readGolden = Just <$> do
    hasWarn <- doesFileExist warnFile
    hasErr  <- doesFileExist errFile
    if | hasWarn && hasErr -> error "Cannot have both .warn and .err file"
       | hasWarn           -> TestWarning <$> readTextFile warnFile
       | hasErr            -> TestFailure <$> readTextFile errFile
       | otherwise         -> pure TestSuccess

  doRun = do
    let agdaArgs = ["-v0", "-i" ++ testDir, "-itest/"
                   , agdaFile, "--ignore-interfaces", "--no-libraries"
                   ]
    (res, ret) <- runAgdaWithOptions testName agdaArgs (Just flagFile) Nothing
    pure $ case ret of
      AgdaSuccess Nothing  -> TestSuccess
      AgdaSuccess (Just w) -> TestWarning $ "AGDA_WARNING\n\n" <> w
      AgdaFailure{}        -> TestFailure $ "AGDA_FAILURE\n\n" <> printProgramResult res

  resUpdate :: TestResult -> IO ()
  resUpdate = \case
    TestSuccess   -> pure ()
    TestWarning w -> writeTextFile warnFile w
    TestFailure e -> writeTextFile errFile e

printTestResult :: TestResult -> T.Text
printTestResult = \case
  TestSuccess   -> "AGDA_SUCCESS\n\n"
  TestWarning w -> w
  TestFailure p -> p

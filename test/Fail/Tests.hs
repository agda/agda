{-# LANGUAGE DoAndIfThenElse   #-}

module Fail.Tests where

import qualified Data.ByteString as BS
import Data.Monoid ((<>))
import qualified Data.Text as T
import Data.Text.Encoding

import System.Directory
import System.Exit
import System.FilePath
import System.IO.Temp

import Test.Tasty
import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced
  (readFileMaybe, goldenTest1, GDiff (..), GShow (..))

import Utils

testDir :: FilePath
testDir = "test" </> "Fail"

tests :: IO TestTree
tests = do
  inpFiles <- getAgdaFilesInDir NonRec testDir
  return $ testGroup "Fail" $
    [ testGroup "customised" [ issue2649, nestedProjectRoots ]]
    ++ map mkFailTest inpFiles

data TestResult
  = TestResult T.Text -- the cleaned stdout
  | TestUnexpectedSuccess ProgramResult

mkFailTest :: FilePath -- inp file
    -> TestTree
mkFailTest inp =
  goldenTest1 testName readGolden (printTestResult <$> doRun) resDiff resShow updGolden
--  goldenVsAction testName goldenFile doRun printTestResult
  where testName   = asTestName testDir inp
        goldenFile = dropAgdaExtension inp <.> ".err"
        flagFile   = dropAgdaExtension inp <.> ".flags"

        readGolden = readTextFileMaybe goldenFile
        updGolden  = writeTextFile goldenFile

        doRun = do
          flags <- maybe [] (T.unpack . decodeUtf8) <$> readFileMaybe flagFile
          let agdaArgs = ["-v0", "-i" ++ testDir, "-itest/" , inp, "--ignore-interfaces", "--no-libraries"] ++ words flags
          readAgdaProcessWithExitCode agdaArgs T.empty >>= expectFail

issue2649 :: TestTree
issue2649 = goldenTest1 "Issue2649" (readTextFileMaybe goldenFile)
  doRun resDiff resShow (writeTextFile goldenFile)
  where
    dir = testDir </> "customised"
    goldenFile = dir </> "Issue2649.err"
    doRun = do
      _  <- readAgdaProcessWithExitCode
              ["--no-libraries", "-i" ++ dir, dir </> "Issue2649-1.agda"]
              T.empty
      _  <- readAgdaProcessWithExitCode
              ["--no-libraries", "-i" ++ dir, dir </> "Issue2649-2.agda"]
              T.empty
      fmap printTestResult . expectFail =<< do
            readAgdaProcessWithExitCode
              ["--no-libraries", "-i" ++ dir, dir </> "Issue2649.agda"]
              T.empty

nestedProjectRoots :: TestTree
nestedProjectRoots = goldenTest1 "NestedProjectRoots" (readTextFileMaybe goldenFile)
  doRun resDiff resShow (writeTextFile goldenFile)
  where
    dir = testDir </> "customised"
    goldenFile = dir </> "NestedProjectRoots.err"
    doRun = do
      r1 <- readAgdaProcessWithExitCode
              ["--ignore-interfaces", "--no-libraries", "-i" ++ dir, "-i" ++ dir </> "Imports", dir </> "NestedProjectRoots.agda"]
              T.empty >>= fmap printTestResult . expectFail
      r2 <- readAgdaProcessWithExitCode
              ["--no-libraries", "-i" ++ dir </> "Imports", dir </> "Imports" </> "A.agda"]
              T.empty >>= expectOk
      r3 <- readAgdaProcessWithExitCode
              ["--no-libraries", "-i" ++ dir, "-i" ++ dir </> "Imports", dir </> "NestedProjectRoots.agda"]
              T.empty >>= fmap printTestResult . expectFail
      return $ r1 `T.append` r2 `T.append` r3

expectOk :: ProgramResult -> IO T.Text
expectOk (ExitSuccess, stdout, _) = pure stdout
expectOk p = return $ "UNEXPECTED_SUCCESS\n\n" `T.append` printProcResult p

expectFail :: ProgramResult -> IO TestResult
expectFail res@(ret, stdout, _) = pure $
  if ret == ExitSuccess
  then TestUnexpectedSuccess res
  else TestResult stdout

-- | Treats newlines or consecutive whitespaces as one single whitespace.
--
-- Philipp20150923: On travis lines are wrapped at different positions sometimes.
-- It's not really clear to me why this happens, but just ignoring line breaks
-- for comparing the results should be fine.
resDiff :: T.Text -> T.Text -> GDiff
resDiff t1 t2 =
  if strip t1 == strip t2
    then
      Equal
    else
      DiffText Nothing t1 t2
  where
    strip = replace (mkRegex " +") " " . replace (mkRegex "(\n|\r)") " "

resShow :: T.Text -> GShow
resShow = ShowText

printTestResult :: TestResult -> T.Text
printTestResult (TestResult t)            = t
printTestResult (TestUnexpectedSuccess p) = "AGDA_UNEXPECTED_SUCCESS\n\n" <> printProcResult p

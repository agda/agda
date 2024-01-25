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
  (readFileMaybe, goldenTest1, goldenTestIO1, GDiff (..), GShow (..))

import Utils

import Agda.Utils.Functor ((<&>), for)

testDir :: FilePath
testDir = "test" </> "Fail"

tests :: IO TestTree
tests = do
  inpFiles <- getAgdaFilesInDir NonRec testDir
  typeBasedTerminationFiles <- getAgdaFilesInDir NonRec $ testDir </> "TypeBasedTermination"
  return $ testGroup "Fail" $ concat $
    -- A list written with ':' to quickly switch lines
    map mkFailTest inpFiles :
    -- Type-based-termination tests are kept separately in order to being able access them independently
    map mkFailTest typeBasedTerminationFiles :
    -- The some of the customized tests fail with agda-quicker
    -- (because they refer to the name of the Agda executable),
    -- so put them last.
    customizedTests :
    []
  where
  customizedTests =
    [ testGroup "customised" $
        issue6465 :
        issue5508 :
        issue5101 :
        issue4671 :
        issue2649 :
        nestedProjectRoots :
        []
    ]

data TestResult
  = TestResult T.Text -- the cleaned stdout
  | TestUnexpectedSuccess ProgramResult

mkFailTest
  :: FilePath -- ^ Input file (Agda file).
  -> TestTree
mkFailTest agdaFile =
  goldenTestIO1
    testName
    readGolden
    (printTestResult <$> doRun)
    (textDiffWithTouch agdaFile)
    (pure . ShowText)
    (Just updGolden)
  where
  testName   = asTestName testDir agdaFile
  baseName   = dropAgdaExtension agdaFile
  varFile    = baseName <.> "vars"
  flagFile   = baseName <.> "flags"
  goldenFile = baseName <.> "err"

  readGolden = readTextFileMaybe goldenFile
  updGolden  = writeTextFile goldenFile

  doRun = do
    let agdaArgs = [ "-v0", "-vwarning:1", "-i" ++ testDir, "-itest/", agdaFile
                   , "--ignore-interfaces", "--no-libraries"
                   , "--double-check"
                   ]
    runAgdaWithOptions testName agdaArgs (Just flagFile) (Just varFile)
      <&> expectFail

-- | A test for case-insensitivity of the file system.
caseInsensitiveFileSystem :: IO Bool
caseInsensitiveFileSystem = fst <$> caseInsensitiveFileSystem4671

-- | A test for case-insensitivity of the file system, using data of test 4671.
caseInsensitiveFileSystem4671 :: IO (Bool, FilePath)
caseInsensitiveFileSystem4671 = do
  b <- doesFileExist goldenFileInsens'
  return (b, if b then goldenFileInsens else goldenFileSens)
  where
    dir = testDir </> "customised"
    goldenFileSens    = dir </> "Issue4671.err.case-sensitive"
    goldenFileInsens  = dir </> "Issue4671.err.case-insensitive"
    goldenFileInsens' = dir </> "Issue4671.err.cAsE-inSensitive" -- case variant, to test file system

issue6465 :: TestTree
issue6465 =
  goldenTest1
    name
    (readTextFileMaybe goldenFile)
    doRun
    textDiff
    ShowText
    (writeTextFile goldenFile)
  where
    name       = "Issue6465"
    dir        = testDir </> "customised"
    goldenFile = dir </> name <.> "err"
    doRun = do
      let agdaArgs file =
            [ "-v0"
            , "--no-default-libraries"
            , "-i" ++ dir
            , "-i" ++ dir </> name
            , dir </> file
            ]
      runAgdaWithOptions
        name (agdaArgs (name <.> "agda")) Nothing Nothing
        <&> printTestResult . expectFail

issue4671 :: TestTree
issue4671 =
  goldenTest1
    "Issue4671"
    (readTextFileMaybe =<< goldenFile)
    doRun
    textDiff
    ShowText
    (\ res -> goldenFile >>= (`writeTextFile` res))
  where
    dir = testDir </> "customised"
    goldenFile = snd <$> caseInsensitiveFileSystem4671
      -- Query case-variant to detect case-sensitivity of the FS.
      -- Note: since we expect the .err file to exists, we cannot
      -- use this test to interactively create a non-existing golden value.

    doRun = do
      let agdaArgs file = [ "-v0", "--no-libraries", "-i" ++ dir, dir </> file ]
      runAgdaWithOptions "Issue4671" (agdaArgs "Issue4671.agda") Nothing Nothing
        <&> printTestResult . expectFail

issue5508 :: TestTree
issue5508 =
  goldenTest1
    "iSSue5508"
    (readTextFileMaybe =<< goldenFile)
    doRun
    textDiff
    ShowText
    (\ res -> goldenFile >>= (`writeTextFile` res))
  where
    dir = testDir </> "customised"
    goldenFile = caseInsensitiveFileSystem <&> (dir </>) . \case
      True  -> "iSSue5508.err.case-insensitive"
      False -> "iSSue5508.err.case-sensitive"
      -- Query case-variant to detect case-sensitivity of the FS.
      -- Note: since we expect the .err file to exists, we cannot
      -- use this test to interactively *create* a non-existing golden value.
      -- However, it can be updated...

    doRun = do
      let agdaArgs file = [ "-v0", "--no-libraries", "-i" ++ dir, dir </> file ]
      runAgdaWithOptions "iSSue5508" (agdaArgs "iSSue5508.agda") Nothing Nothing
        <&> printTestResult . expectFail

-- The only customization here is that these do not have input .agda files,
-- because the front-end interactors do not accept them.
-- This runs the same as a normal test, but won't be auto-discovered because
-- currently test discovery searches only for the .agda source.
issue5101 :: TestTree
issue5101 = testGroup "Issue5101" $
  for suffixes $ \s -> do
    let testName = "OnlyScopeChecking" ++ s
    let goldenFile = dir </> testName <.> "err"
    let flagsFile = dir </> testName <.> "flags"
    let agdaArgs = ["-v0", "--no-libraries", "-i" ++ dir]
    let doRun = runAgdaWithOptions testName agdaArgs (Just flagsFile) Nothing <&> printTestResult . expectFail
    goldenTest1
      testName
      (readTextFileMaybe goldenFile)
      doRun
      textDiff
      ShowText
      (writeTextFile goldenFile)
  where
  dir = testDir
  suffixes = ["Repl", "Emacs", "JSON", "Vim"]

issue2649 :: TestTree
issue2649 =
  goldenTest1
    "Issue2649"
    (readTextFileMaybe goldenFile)
    doRun
    textDiff
    ShowText
    (writeTextFile goldenFile)
  where
    dir = testDir </> "customised"
    goldenFile = dir </> "Issue2649.err"
    doRun = do
      let agdaArgs file = ["--no-libraries", "-i" ++ dir, dir </> file ]
      _  <- runAgdaWithOptions "Issue2649-1" (agdaArgs "Issue2649-1.agda") Nothing Nothing
      _  <- runAgdaWithOptions "Issue2649-2" (agdaArgs "Issue2649-2.agda") Nothing Nothing
      runAgdaWithOptions "Issue2649"   (agdaArgs "Issue2649.agda")   Nothing Nothing
        <&> printTestResult . expectFail

nestedProjectRoots :: TestTree
nestedProjectRoots =
  goldenTest1
    "NestedProjectRoots"
    (readTextFileMaybe goldenFile)
    doRun
    textDiff
    ShowText
    (writeTextFile goldenFile)
  where
    dir = testDir </> "customised"
    goldenFile = dir </> "NestedProjectRoots.err"
    doRun = do
      let agdaArgs file = ["--no-libraries", "-i" ++ dir </> "Imports", dir </> file]
      let run extra = do
            runAgdaWithOptions "NestedProjectRoots"
              (extra ++ [ "-i" ++ dir ] ++ agdaArgs "NestedProjectRoots.agda")
              Nothing Nothing
              <&> printTestResult . expectFail
      -- Run without interfaces; should fail.
      r1 <- run [ "--ignore-interfaces" ]
      -- Create interface file
      r2 <- runAgdaWithOptions "Imports.A"
              ("-v 0" : agdaArgs ("Imports" </> "A.agda")) Nothing Nothing
              <&> expectOk
      -- Run again with interface; should still fail.
      r3 <- run []
      return $ r1 `T.append` r2 `T.append` r3

expectOk :: (ProgramResult, AgdaResult) -> T.Text
expectOk (res, ret) = case ret of
  AgdaSuccess{} -> stdOut res
  AgdaFailure{} -> "AGDA_UNEXPECTED_FAILURE\n\n" <> printProgramResult res

expectFail :: (ProgramResult, AgdaResult) -> TestResult
expectFail (res, ret) = case ret of
  AgdaSuccess{} -> TestUnexpectedSuccess res
  -- If it's a type error, we do not print the exit code
  AgdaFailure _ (Just TCMError) -> TestResult $ stdOut res
  -- Otherwise, we print all the output
  AgdaFailure{}                 -> TestResult $ printProgramResult res


printTestResult :: TestResult -> T.Text
printTestResult = \case
  TestResult t            -> t
  TestUnexpectedSuccess p -> "AGDA_UNEXPECTED_SUCCESS\n\n" <> printProgramResult p

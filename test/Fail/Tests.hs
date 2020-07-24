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
import System.PosixCompat.Files (touchFile)

import Test.Tasty
import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced
  (readFileMaybe, goldenTest1, goldenTestIO1, GDiff (..), GShow (..))

import Utils

import Agda.Utils.Functor ((<&>))

testDir :: FilePath
testDir = "test" </> "Fail"

tests :: IO TestTree
tests = do
  inpFiles <- getAgdaFilesInDir NonRec testDir
  return $ testGroup "Fail" $ concat
    [ map mkFailTest inpFiles
    , [ testGroup "customised" [ issue2649, nestedProjectRoots ]]
    ]

data TestResult
  = TestResult T.Text -- the cleaned stdout
  | TestUnexpectedSuccess ProgramResult

mkFailTest
  :: FilePath -- ^ Input file (Agda file).
  -> TestTree
mkFailTest agdaFile =
  goldenTestIO1 testName readGolden (printTestResult <$> doRun) resDiff (pure . resShow) $ Just updGolden
  where
  testName   = asTestName testDir agdaFile
  goldenFile = dropAgdaExtension agdaFile <.> ".err"
  flagFile   = dropAgdaExtension agdaFile <.> ".flags"

  readGolden = readTextFileMaybe goldenFile
  updGolden  = writeTextFile goldenFile

  doRun = do
    let agdaArgs = ["-v0", "-i" ++ testDir, "-itest/" , agdaFile
                   , "--ignore-interfaces", "--no-libraries"]
                   ++ [ "--double-check" | not (testName `elem` noDoubleCheckTests) ]
    runAgdaWithOptions testName agdaArgs (Just flagFile) Nothing
      <&> expectFail

  -- | Treats newlines or consecutive whitespaces as one single whitespace.
  --
  -- Philipp20150923: On travis lines are wrapped at different positions sometimes.
  -- It's not really clear to me why this happens, but just ignoring line breaks
  -- for comparing the results should be fine.
  resDiff :: T.Text -> T.Text -> IO GDiff
  resDiff t1 t2
    | stripConsecutiveWhiteSpace t1 == stripConsecutiveWhiteSpace t2 = return Equal
    | otherwise = do
        -- Andreas, 2020-06-09, issue #4736
        -- If the output has changed, the test case is "interesting"
        -- regardless of whether the golden value is updated or not.
        -- Thus, we touch the agdaFile to have it sorted up in the next
        -- test run.
        -- -- putStrLn $ "TOUCHING " ++ agdaFile
        touchFile agdaFile
        return $ DiffText Nothing t1 t2


issue2649 :: TestTree
issue2649 = goldenTest1 "Issue2649" (readTextFileMaybe goldenFile)
  doRun resDiff resShow (writeTextFile goldenFile)
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
nestedProjectRoots = goldenTest1 "NestedProjectRoots" (readTextFileMaybe goldenFile)
  doRun resDiff resShow (writeTextFile goldenFile)
  where
    dir = testDir </> "customised"
    goldenFile = dir </> "NestedProjectRoots.err"
    doRun = do
      let agdaArgs file = ["--no-libraries", "-i" ++ dir </> "Imports", dir </> file]
      r1 <- runAgdaWithOptions "NestedProjectRoots"
              ("--ignore-interfaces" : ("-i" ++ dir) : agdaArgs "NestedProjectRoots.agda")
              Nothing Nothing
              <&> printTestResult . expectFail
      r2 <- runAgdaWithOptions "Imports.A" (agdaArgs ("Imports" </> "A.agda")) Nothing Nothing
              <&> expectOk
      r3 <- runAgdaWithOptions "NestedProjectRoots"
              (("-i" ++ dir) : agdaArgs "NestedProjectRoots.agda")
              Nothing Nothing
              <&> printTestResult . expectFail
      return $ r1 `T.append` r2 `T.append` r3

expectOk :: (ProgramResult, AgdaResult) -> T.Text
expectOk (res, ret) = case ret of
  AgdaSuccess{} -> stdOut res
  _             -> "UNEXPECTED_SUCCESS\n\n" <> printProgramResult res

expectFail :: (ProgramResult, AgdaResult) -> TestResult
expectFail (res, ret) = case ret of
  AgdaSuccess{} -> TestUnexpectedSuccess res
  -- If it's a type error, we do not print the exit code
  AgdaFailure _ (Just TCMError) -> TestResult $ stdOut res
  -- Otherwise, we print all the output
  AgdaFailure{}                 -> TestResult $ printProgramResult res

-- | Treats newlines or consecutive whitespaces as one single whitespace.
--
-- Philipp20150923: On travis lines are wrapped at different positions sometimes.
-- It's not really clear to me why this happens, but just ignoring line breaks
-- for comparing the results should be fine.
resDiff :: T.Text -> T.Text -> GDiff
resDiff t1 t2 =
  if stripConsecutiveWhiteSpace t1 == stripConsecutiveWhiteSpace t2
    then
      Equal
    else
      DiffText Nothing t1 t2


-- | Converts newlines and consecutive whitespaces into one single whitespace.
--
stripConsecutiveWhiteSpace :: T.Text -> T.Text
stripConsecutiveWhiteSpace
  = replace (mkRegex " +")      " "
  . replace (mkRegex "(\n|\r)") " "

resShow :: T.Text -> GShow
resShow = ShowText

printTestResult :: TestResult -> T.Text
printTestResult = \case
  TestResult t            -> t
  TestUnexpectedSuccess p -> "AGDA_UNEXPECTED_SUCCESS\n\n" <> printProgramResult p

noDoubleCheckTests :: [String]
noDoubleCheckTests =
  [ "Issue3982"
  , "SizedTypesScopeViolationInMeta"
  , "CheckSizeMetaBounds"
  , "ConfluenceNestedOverlap"
  , "ConfluenceTypeLevelReduction"
  , "ConstructorHeadedDivergenceIn2-2-10"
  , "FrozenMVar"
  , "HoTTCompatibleWithSizeBasedTerminationMaximeDenes"
  , "Issue118Comment9"
  , "Issue1209-2"
  , "Issue1258"
  , "Issue1445-2"
  , "Issue1445-3"
  , "Issue1467"
  , "Issue1523a"
  , "Issue1615"
  , "Issue1974"
  , "Issue1976-constraints"
  , "Issue2450"
  , "Issue2710"
  , "Issue2941"
  , "Issue2944"
  , "Issue2985-1"
  , "Issue2985-2"
  , "Issue2993"
  , "Issue300"
  , "Issue3067"
  , "Issue3114"
  , "Issue3401"
  , "Issue3431"
  , "Issue399"
  , "Issue4118"
  , "Issue418"
  , "Issue431"
  , "Issue431b"
  , "Issue483c"
  , "Issue485"
  , "Issue585-11"
  , "Issue585t"
  , "Issue659"
  , "Issue691"
  , "Issue796"
  , "Issue796o"
  , "Issue878"
  , "Issue920a"
  , "Issue921"
  , "NoConstraints"
  , "RewriteExt-confluence"
  , "SizeUnsolvedConstraintsInTypeSignature"
  , "SizedBTree"
  , "SizedTypesFunctionFromSuccSize"
  , "SizedTypesRigidVarClash"
  , "SizedTypesScopeExtrusion"
  , "SizedTypesVarSwap"
  , "WrongPolarity"
  ]


module CubicalSucceed.Tests where

import qualified Data.Text as T
import Data.List (isInfixOf)
import Data.Monoid ((<>))

import System.Exit
import System.FilePath

import Test.Tasty                 ( testGroup, TestTree )
import Test.Tasty.Silver          ( printProcResult )
import Test.Tasty.Silver.Advanced ( GDiff(..), GShow(..), goldenTestIO1 )
import Test.Tasty.Silver.Filter   ( RegexFilter(RFInclude) )

import Utils

testDir :: FilePath
testDir = "test" </> "CubicalSucceed"

disabledTests :: [RegexFilter]
disabledTests =
  []

-- | Filter out files that contain one of these words.
notTests :: [String]
notTests =
  []

tests :: IO TestTree
tests = do
  let isTest file = not $ any (`isInfixOf` file) notTests
  inpFiles <- filter isTest <$> getAgdaFilesInDir Rec testDir

  let tests' :: [TestTree]
      tests' = map mkCubicalSucceedTest inpFiles

  return $ testGroup "CubicalSucceed" tests'

rtsOptions :: [String]
rtsOptions = [ "+RTS", "-H1G", "-M1.5G", "-RTS" ]

data TestResult
  = TestSuccess
  | TestUnexpectedFail ProgramResult

mkCubicalSucceedTest :: FilePath  -- ^ Agda file to test.
                 -> TestTree
mkCubicalSucceedTest agdaFile =
  goldenTestIO1
    testName
    readGolden
    (printAgdaResult <$> doRun)
    (textDiffWithTouch agdaFile)
    (return . ShowText)
    Nothing
  where
    testName :: String
    testName = asTestName testDir agdaFile

    -- We don't really have a golden file. Just use a dummy update
    -- function. TODO extend tasty-silver to handle this use case
    -- properly
    readGolden :: IO (Maybe T.Text)
    readGolden = return $ Just $ printAgdaResult TestSuccess

    doRun :: IO TestResult
    doRun = do
      -- ASR (04 January 2016). We don't use the @--ignore-interfaces@
      -- option for avoiding type-check the cubical library in every
      -- test-case. The interface files are deleted in the Makefile.
      let agdaArgs :: AgdaArgs
          agdaArgs = [ "-v0"
                     , "-i" ++ testDir
                     , "-i" ++ "cubical"
                     , "--no-libraries"
                     , "--cubical"
                     , agdaFile
                     ] ++ rtsOptions
      (res, ret) <- runAgdaWithOptions testName agdaArgs Nothing Nothing
      pure $ case ret of
        AgdaSuccess{} -> TestSuccess -- TODO: fail if unexpected warnings?
        AgdaFailure{} -> TestUnexpectedFail res

printAgdaResult :: TestResult -> T.Text
printAgdaResult = \case
  TestSuccess          -> "AGDA_SUCCESS"
  TestUnexpectedFail p -> "AGDA_UNEXPECTED_FAIL\n\n" <> printProgramResult p

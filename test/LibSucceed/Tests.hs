
module LibSucceed.Tests where

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
testDir = "test" </> "LibSucceed"

disabledTests :: [RegexFilter]
disabledTests =
  []

notTests :: [String]
notTests =
  [ -- These modules are imported by Issue784.agda
    "Issue784/"
    -- These modules are imported by Issue846.agda
  , "Issue846/"
    -- These modules are imported by Issue854.agda
  , "Issue854/"
    -- This module is imported by DeBruijnExSubstSized.agda
  , "Termination-Sized-DeBruijnBase"
  ]

tests :: IO TestTree
tests = do
  let isTest file = not $ any (`isInfixOf` file) notTests
  inpFiles <- filter isTest <$> getAgdaFilesInDir Rec testDir

  let tests' :: [TestTree]
      tests' = map mkLibSucceedTest inpFiles

  return $ testGroup "LibSucceed" tests'

rtsOptions :: [String]
rtsOptions = [ "+RTS", "-H1G", "-M1.5G", "-RTS" ]

data TestResult
  = TestSuccess
  | TestUnexpectedFail ProgramResult

mkLibSucceedTest :: FilePath  -- inp file
                 -> TestTree
mkLibSucceedTest inp =
  goldenTestIO1 testName readGolden (printAgdaResult <$> doRun) resDiff resShow Nothing
  where
    testName :: String
    testName = asTestName testDir inp

    -- We don't really have a golden file. Just use a dummy update
    -- function. TODO extend tasty-silver to handle this use case
    -- properly
    readGolden :: IO (Maybe T.Text)
    readGolden = return $ Just $ printAgdaResult TestSuccess

    doRun :: IO TestResult
    doRun = do
      -- ASR (04 January 2016). We don't use the @--ignore-interfaces@
      -- option for avoiding type-check the standard library in every
      -- test-case. The interface files are deleted in the Makefile.
      let agdaArgs :: AgdaArgs
          agdaArgs = [ "-v0"
                     , "-i" ++ testDir
                     , "-i" ++ "std-lib/src"
                     , "--no-libraries"
                     , inp
                     ] ++ rtsOptions
      (res, ret) <- runAgdaWithOptions testName agdaArgs Nothing Nothing
      pure $ case ret of
        AgdaSuccess{} -> TestSuccess -- TODO: fail if unexpected warnings?
        AgdaFailure{} -> TestUnexpectedFail res

resDiff :: T.Text -> T.Text -> IO GDiff
resDiff t1 t2 =
  if t1 == t2
    then
      return Equal
    else
      return $ DiffText Nothing t1 t2

resShow :: T.Text -> IO GShow
resShow = return . ShowText

printAgdaResult :: TestResult -> T.Text
printAgdaResult TestSuccess            = "AGDA_SUCCESS"
printAgdaResult (TestUnexpectedFail p) = "AGDA_UNEXPECTED_FAIL\n\n" <> printProgramResult p

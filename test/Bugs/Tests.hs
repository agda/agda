module Bugs.Tests where

import Test.Tasty
import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced
       (readFileMaybe, GDiff(..), GShow(..), goldenTest1)
import System.IO.Temp
import System.FilePath
import qualified Data.Text as T
import Data.Text.Encoding
import System.Exit
import System.Directory
import qualified Data.ByteString as BS

import Utils

testDir :: FilePath
testDir = "test" </> "Bugs"

tests :: IO TestTree
tests = do
  inpFiles <- getAgdaFilesInDir NonRec testDir
  return $ testGroup "Bugs" $
    map mkFailTest inpFiles

data AgdaResult
  = AgdaFail
  | AgdaUnexpectedSuccess ProgramResult
  deriving (Eq)

mkFailTest :: FilePath -- inp file
           -> TestTree
mkFailTest inp =
  goldenTest1 testName (pure $ Just AgdaFail) doRun resDiff resShow
              (const $ pure ())

  where testName   = asTestName testDir inp
        flagFile   = dropAgdaExtension inp <.> ".flags"

        doRun = do
          flags <- maybe [] (T.unpack . decodeUtf8) <$> readFileMaybe flagFile
          let agdaArgs = ["-v0", "-i" ++ testDir, "-itest/"
                         , inp, "--ignore-interfaces", "--no-libraries"
                         ] ++ words flags
          expectFail <$> readAgdaProcessWithExitCode agdaArgs T.empty

expectFail :: ProgramResult -> AgdaResult
expectFail res@(ret, stdout, _)
  | ret == ExitSuccess = AgdaUnexpectedSuccess res
  | otherwise          = AgdaFail

resDiff :: AgdaResult -> AgdaResult -> GDiff
resDiff t1 t2
  | t1 == t2  = Equal
  | otherwise = DiffText Nothing (printAgdaResult t1) (printAgdaResult t2)

resShow :: AgdaResult -> GShow
resShow = ShowText . printAgdaResult

printAgdaResult :: AgdaResult -> T.Text
printAgdaResult = \case
  AgdaFail                -> ""
  AgdaUnexpectedSuccess p -> "AGDA_UNEXPECTED_SUCCESS\n\n" <> printProcResult p

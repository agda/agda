{-# LANGUAGE DoAndIfThenElse   #-}

module Succeed.Tests where

import Data.List
import Data.Maybe (isJust, fromMaybe)
import Data.Monoid ((<>))
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Text.Encoding

import Test.Tasty
import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced
  (readFileMaybe, goldenTestIO1, GDiff (..), GShow (..))

import System.Directory
import System.Exit
import System.FilePath
import System.IO.Temp


import Utils

testDir :: FilePath
testDir = "test" </> "Succeed"

tests :: IO TestTree
tests = do
  inpFiles <- getAgdaFilesInDir Rec testDir

  let extraOpts = [ "--ignore-interfaces" , "--vim" ]
  let tests' = map (mkSucceedTest extraOpts testDir) inpFiles

  return $ testGroup "Succeed" tests'

data TestResult
  = TestSuccess
  | TestSuccessWithWarnings T.Text -- the cleaned stdout
  | TestUnexpectedFail ProgramResult
  | TestWrongDotOutput T.Text

mkSucceedTest
  :: AgdaArgs -- ^ Extra options to Agda.
  -> FilePath -- ^ Test directory.
  -> FilePath -- ^ Input file.
  -> TestTree
mkSucceedTest extraOpts dir inp =
  goldenTestIO1 testName readGolden (printTestResult <$> doRun) resDiff resShow updGolden
--  goldenVsAction testName goldenFile doRun printAgdaResult
  where testName = asTestName dir inp
        flagFile = dropAgdaExtension inp <.> ".flags"
        warnFile = dropAgdaExtension inp <.> ".warn"

        -- Unless we have a .warn file, we don't really have a golden
        -- file. Just use a dummy update function.
        -- TODO extend tasty-silver to handle this use case properly
        readGolden = do
          warnExists <- doesFileExist warnFile
          if warnExists then readTextFileMaybe warnFile
                        else return $ Just $ printTestResult TestSuccess

        updGolden = Just $ writeTextFile warnFile

        doRun = do
          let agdaArgs = [ "-v0", "-i" ++ dir, "-itest/" , inp
                         , "--no-libraries"
                         , "-vimpossible:10" -- BEWARE: no spaces allowed here
                         , "-vwarning:1"
                         ] ++ [ "--double-check" | not (testName `elem` noDoubleCheckTests) ]
                           ++ extraOpts

          (res, ret) <- runAgdaWithOptions testName agdaArgs (Just flagFile)
          case ret of
            AgdaSuccess{} | testName == "Issue481" -> do
              dotOrig <- TIO.readFile (dir </> "Issue481.dot.orig")
              dot <- TIO.readFile "Issue481.dot"
              removeFile "Issue481.dot"
              if dot == dotOrig
                then
                  return $ TestSuccess
                else
                  return $ TestWrongDotOutput dot
            AgdaSuccess warn -> do
              warnExists <- doesFileExist warnFile
              return $
                if warnExists || isJust warn
                then TestSuccessWithWarnings $ stdOut res -- TODO: distinguish log vs. warn?
                else TestSuccess
            AgdaFailure -> return $ TestUnexpectedFail res

resDiff :: T.Text -> T.Text -> IO GDiff
resDiff t1 t2 =
  if T.words t1 == T.words t2
    then
      return Equal
    else
      return $ DiffText Nothing t1 t2

resShow :: T.Text -> IO GShow
resShow = return . ShowText

printTestResult :: TestResult -> T.Text
printTestResult r = case r of
  TestSuccess               -> "AGDA_SUCCESS\n\n"
  TestSuccessWithWarnings t -> t
  TestUnexpectedFail p      -> "AGDA_UNEXPECTED_FAIL\n\n" <> printProgramResult p
  TestWrongDotOutput t      -> "AGDA_WRONG_DOT_OUTPUT\n\n" <> t

-- List of test cases that do not pass the --double-check yet
noDoubleCheckTests :: [String]
noDoubleCheckTests =
  [ "Cumulativity"
  , "CompileTimeInlining"
  , "Conat-Sized"
  , "CopatternTrailingImplicit"
  , "CubicalPrims"
  , "DataPolarity"
  , "Issue1038"
  , "Issue1099"
  , "Issue1203"
  , "Issue1209-4"
  , "Issue1209-5"
  , "Issue1209-6"
  , "Issue1292b"
  , "Issue1409"
  , "Issue1470"
  , "Issue1523a"
  , "Issue1551"
  , "Issue1796rewrite"
  , "Issue1817"
  , "Issue1914"
  , "Issue2046"
  , "Issue2054"
  , "Issue2257"
  , "Issue2257b"
  , "Issue2429-subtyping"
  , "Issue2484-1"
  , "Issue2484-2"
  , "Issue2484-3"
  , "Issue2484-4"
  , "Issue2484-5"
  , "Issue2484-6"
  , "Issue2484-7"
  , "Issue2484-8"
  , "Issue2484-9"
  , "Issue2484-10"
  , "Issue2484-11"
  , "Issue2554-size-mutual"
  , "Issue2554-size-plus2"
  , "Issue2558"
  , "Issue2917"
  , "Issue298"
  , "Issue298b"
  , "Issue3577"
  , "Issue3601"
  , "Issue3639"
  , "Issue709"
  , "OutStream"
  , "RewriteExt"
  , "Rose"
  , "SizedCoinductiveRecords"
  , "SizedNatNew"
  , "SizedQuicksort"
  , "SizedTypesExtendedLambda"
  , "SizedTypesMergeSort"
  , "SizedTypesMutual"
  , "language-sized-types"
  ]

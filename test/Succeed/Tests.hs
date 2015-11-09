{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE OverloadedStrings #-}
module Succeed.Tests where

import Test.Tasty
import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced (readFileMaybe, goldenTest1, GDiff (..), GShow (..))
import Data.Maybe
import System.FilePath
import System.IO.Temp
import qualified System.Process.Text as PT
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Text.Encoding
import System.Exit
import Data.List
import System.Directory

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ((<$>))
#endif

import Utils


testDir :: FilePath
testDir = "test" </> "Succeed"

tests :: IO TestTree
tests = do
  inpFiles <- getAgdaFilesInDir Rec testDir
  agdaBin <- getAgdaBin

  let tests' = map (mkSucceedTest agdaBin) inpFiles

  return $ testGroup "Succeed" tests'

data AgdaResult
  = AgdaSuccess
  | AgdaUnexpectedFail ProgramResult
  | AgdaWrongDotOutput T.Text



mkSucceedTest :: FilePath -- agda binary
    -> FilePath -- inp file
    -> TestTree
mkSucceedTest agdaBin inp = do
  goldenTest1 testName readGolden (printAgdaResult <$> doRun) resDiff resShow updGolden
--  goldenVsAction testName goldenFile doRun printAgdaResult
  where testName = asTestName testDir inp
        flagFile = (dropExtension inp) <.> ".flags"

        -- we don't really have a golden file. Just use
        -- a dummy update function.
        -- TODO extend tasty-silver to handle this use case properly
        readGolden = return $ Just $ printAgdaResult AgdaSuccess
        updGolden = \_ -> return ()

        doRun = (do
          flags <- fromMaybe [] . fmap (T.unpack . decodeUtf8) <$> readFileMaybe flagFile
          let agdaArgs = [ "-v0", "-i" ++ testDir, "-itest/" , inp
                         , "--ignore-interfaces", "--vim"
                         , "--no-default-libraries"
                         ] ++
                         words flags
          let run = \extraArgs -> PT.readProcessWithExitCode agdaBin (agdaArgs ++ extraArgs) T.empty

          res@(ret, _, _) <-
            if "--compile" `isInfixOf` flags
              then do
                withTempDirectory testDir ("MAZ_compile_" ++ testName) (\compDir -> do
                  run ["--compile-dir=" ++ compDir]
                  )
              else
                run []

          case ret of
            ExitSuccess | testName == "Issue481" -> do
              dotOrig <- TIO.readFile (testDir </> "Issue481.dot.orig")
              dot <- TIO.readFile "Issue481.dot"
              removeFile "Issue481.dot"
              if dot == dotOrig
                then
                  return AgdaSuccess
                else
                  return $ AgdaWrongDotOutput dot
            ExitSuccess -> return AgdaSuccess
            _ -> return $ AgdaUnexpectedFail res
          )

resDiff :: T.Text -> T.Text -> GDiff
resDiff t1 t2 =
  if t1 == t2
    then
      Equal
    else
      DiffText Nothing t1 t2

resShow :: T.Text -> GShow
resShow = ShowText

printAgdaResult :: AgdaResult -> T.Text
printAgdaResult (AgdaSuccess) = "AGDA_SUCCESS"
printAgdaResult (AgdaUnexpectedFail p) = "AGDA_UNEXPECTED_FAIL\n\n" `T.append` printProcResult p
printAgdaResult (AgdaWrongDotOutput t) = "AGDA_WRONG_DOT_OUTPUT\n\n" `T.append` t

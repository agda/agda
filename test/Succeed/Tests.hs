{-# LANGUAGE CPP               #-}
{-# LANGUAGE DoAndIfThenElse   #-}
{-# LANGUAGE OverloadedStrings #-}

module Succeed.Tests where

import Test.Tasty
import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced (readFileMaybe, goldenTestIO1, GDiff (..), GShow (..))
import System.FilePath
import System.IO.Temp
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

  let tests' = map mkSucceedTest inpFiles

  return $ testGroup "Succeed" tests'

data AgdaResult
  = AgdaSuccess
  | AgdaUnexpectedFail ProgramResult
  | AgdaWrongDotOutput T.Text

mkSucceedTest :: FilePath -- inp file
    -> TestTree
mkSucceedTest inp =
  goldenTestIO1 testName readGolden (printAgdaResult <$> doRun) resDiff resShow Nothing
--  goldenVsAction testName goldenFile doRun printAgdaResult
  where testName = asTestName testDir inp
        flagFile = dropExtension inp <.> ".flags"

        -- we don't really have a golden file. Just use
        -- a dummy update function.
        -- TODO extend tasty-silver to handle this use case properly
        readGolden = return $ Just $ printAgdaResult AgdaSuccess

        doRun = do
          flags <- maybe [] (T.unpack . decodeUtf8) <$> readFileMaybe flagFile
          let agdaArgs = [ "-v0", "-i" ++ testDir, "-itest/" , inp
                         , "--ignore-interfaces", "--vim"
                         , "--no-default-libraries"
                         , "-v impossible:10"
                         ] ++
                         words flags
          let run = \extraArgs -> readAgdaProcessWithExitCode (agdaArgs ++ extraArgs) T.empty

          res@(ret, _, _) <-
            if "--compile" `isInfixOf` flags
              then
                withTempDirectory testDir ("MAZ_compile_" ++ testName) (\compDir ->
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

resDiff :: T.Text -> T.Text -> IO GDiff
resDiff t1 t2 =
  if t1 == t2
    then
      return Equal
    else
      return $ DiffText Nothing t1 t2

resShow :: T.Text -> IO GShow
resShow = return . ShowText

printAgdaResult :: AgdaResult -> T.Text
printAgdaResult AgdaSuccess            = "AGDA_SUCCESS"
printAgdaResult (AgdaUnexpectedFail p) = "AGDA_UNEXPECTED_FAIL\n\n" `T.append` printProcResult p
printAgdaResult (AgdaWrongDotOutput t) = "AGDA_WRONG_DOT_OUTPUT\n\n" `T.append` t

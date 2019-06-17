{-# LANGUAGE DoAndIfThenElse   #-}

module Succeed.Tests where

import Test.Tasty
import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced (readFileMaybe, goldenTestIO1, GDiff (..), GShow (..))
import System.FilePath
import System.IO.Temp
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Text.Encoding
import Data.Monoid ((<>))
import System.Exit
import Data.List
import System.Directory

import Utils

testDir :: FilePath
testDir = "test" </> "Succeed"

tests :: IO TestTree
tests = do
  inpFiles <- getAgdaFilesInDir Rec testDir

  let extraOpts = [ "--ignore-interfaces" , "--vim" ]
  let tests' = map (mkSucceedTest extraOpts testDir) inpFiles

  return $ testGroup "Succeed" tests'

data AgdaResult
  = AgdaSuccess
  | AgdaSuccessWithWarnings T.Text -- the cleaned stdout
  | AgdaUnexpectedFail ProgramResult
  | AgdaWrongDotOutput T.Text

mkSucceedTest
  :: [String] -- ^ Extra options to Agda.
  -> FilePath -- ^ Test directory.
  -> FilePath -- ^ Input file.
  -> TestTree
mkSucceedTest extraOpts dir inp =
  goldenTestIO1 testName readGolden (printAgdaResult <$> doRun) resDiff resShow updGolden
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
                        else return $ Just $ printAgdaResult AgdaSuccess

        updGolden = Just $ writeTextFile warnFile

        doRun = do
          flags <- maybe [] (T.unpack . decodeUtf8) <$> readFileMaybe flagFile
          let agdaArgs = [ "-v0", "-i" ++ dir, "-itest/" , inp
                         , "--no-libraries"
                         , "-vimpossible:10" -- BEWARE: no spaces allowed here
                         , "-vwarning:1"
                         ] ++
                         extraOpts ++ words flags
          let run = \extraArgs -> readAgdaProcessWithExitCode (agdaArgs ++ extraArgs) T.empty

          res@(ret, stdOut, _) <-
            if "--compile" `isInfixOf` flags
              then
                -- Andreas, 2017-04-14, issue #2317
                -- Create temporary files in system temp directory.
                -- This has the advantage that upon Ctrl-C no junk is left behind
                -- in the Agda directory.
                -- withTempDirectory dir ("MAZ_compile_" ++ testName) (\compDir ->
                withSystemTempDirectory ("MAZ_compile_" ++ testName) (\compDir ->
                  run ["--compile-dir=" ++ compDir]
                  )
              else
                run []

          case ret of
            ExitSuccess | testName == "Issue481" -> do
              dotOrig <- TIO.readFile (dir </> "Issue481.dot.orig")
              dot <- TIO.readFile "Issue481.dot"
              removeFile "Issue481.dot"
              if dot == dotOrig
                then
                  return $ AgdaSuccess
                else
                  return $ AgdaWrongDotOutput dot
            ExitSuccess -> do
              cleanedStdOut <- cleanOutput stdOut
              warnExists    <- doesFileExist warnFile
              return $
                if warnExists || hasWarning cleanedStdOut
                then AgdaSuccessWithWarnings cleanedStdOut
                else AgdaSuccess
            _ -> return $ AgdaUnexpectedFail res

hasWarning :: T.Text -> Bool
hasWarning t =
 "———— All done; warnings encountered ————————————————————————"
 `T.isInfixOf` t

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
printAgdaResult r = case r of
  AgdaSuccess               -> "AGDA_SUCCESS\n\n"
  AgdaSuccessWithWarnings t -> t
  AgdaUnexpectedFail p      -> "AGDA_UNEXPECTED_FAIL\n\n" <> printProcResult p
  AgdaWrongDotOutput t      -> "AGDA_WRONG_DOT_OUTPUT\n\n" <> t


-- Test runner for the "simple" interaction tests.

-- "simple" interaction tests are automatically detected at run-time
-- based on the presence of '.in' files (and no .sh file)
-- and run with a standard test harness which supports limited scripting via '.in' files

module Interaction.Simple.Tests where

import Control.Monad ((>=>))
import Data.List (isSuffixOf, singleton)
import Data.Text (Text)
import Test.Tasty (TestTree)
import System.FilePath (FilePath, dropFileName, takeBaseName, (</>), (-<.>))
import System.Directory (listDirectory, doesFileExist, getCurrentDirectory)
import Data.Maybe (fromMaybe)

import qualified System.Exit                as Exit
import qualified Data.Text                  as T
import qualified Data.Text.IO               as T
import qualified System.Process.Text        as T
import qualified Test.Tasty                 as Tasty
import qualified Test.Tasty.Silver.Advanced as Tasty
import qualified Utils

import Utils (readAgdaProcessWithExitCode, getAgdaFilesInDir, pattern Rec, readFileMaybeText, writeTextFile, textDiffWithTouch, textDiff, runAgdaWithOptions, readAgdaProcessWithCWD)
import Agda.Utils.Monad (filterM)

testDir :: FilePath
testDir = "test" </> "interaction"

tests :: IO TestTree
tests = Tasty.testGroup "Interaction" . singleton <$>
  -- DEBUG: run tests sequentially
  -- Tasty.sequentialTestGroup "simple" Tasty.AllSucceed . map mkSimpleTest
  Tasty.testGroup "simple" . map mkSimpleTest
    <$> getSimplyTestableAgdaFiles testDir

-- Get list of paths to Agda files, which have a .in file next to them,
-- and no .sh file
getSimplyTestableAgdaFiles :: FilePath -> IO [FilePath]
getSimplyTestableAgdaFiles dir = filterM isSimple =<< getAgdaFilesInDir Rec dir
    where
  isSimple :: FilePath -> IO Bool
  isSimple fp = (&&)
    <$>          doesFileExist (fp -<.> "in")
    <*> (not <$> doesFileExist (fp -<.> "sh"))

-- | Helper: call out to `sed` for string operation
sed :: String -> Text -> IO Text
sed cmd str = do
  (_, stdout, _) <- T.readProcessWithExitCode "sed" [cmd] str
  pure stdout

-- | Expand the language of '.in' scripts to strings that are
-- well-formed standard input for `agda --interaction`
expandInScript :: FilePath -> Text -> IO Text
expandInScript fullPathToAgdaFile =
  -- Can't use re with replacements containing backreferences
      sed "s/ioTCM/IOTCM/g"
  >=> sed "s/cmd_give/(cmd_give WithoutForce)/g"
  >=> sed "s/cmd_/Cmd_/g"
  >=> sed "s/showImplicitArgs/ShowImplicitArgs/g"
  >=> sed "s/toggleImplicitArgs/ToggleImplicitArgs/g"
  >=> sed "s/top_command/IOTCM currentFile None Indirect/g"
  >=> sed "s/goal_command \\([0-9]\\+\\) (\\([^)]\\+\\)) \\(\"[^\"]*\"\\)/IOTCM currentFile None Indirect (\\2 \\1 noRange \\3)/g"
  >=> sed "s/goal_command \\([0-9]\\+\\) \\([^ ]\\+\\) \\(\"[^\"]*\"\\)/IOTCM currentFile None Indirect (\\2 \\1 noRange \\3)/g"
  >=> sed ("s:currentFile:\"" <> fullPathToAgdaFile <> "\":g")
  >=> sed ("s+currentFullPath+\"" <> fullPathToAgdaFile <> "\"+g")

-- | Filter the output of running `agda --interaction` to make it
-- more robust across GHC versions etc.
filterOutput :: FilePath -> Text -> Text
filterOutput dir = let  in
  id
  . re "in Agda?-[.0-9]+(-[[:alnum:]]+)?" "«Agda-package»"
  . re "[.]hs:[0-9]+:[0-9]+" ".hs:«line»:«col»"
  . re "\\(agda2-highlight-load-and-delete-action .*\\)" "(agda2-highlight-load-and-delete-action)"
  . re "[^ (\"]*lib.prim" "agda-default-include-path"
  . re parentDir' "../"
  . re dir' ""
  . re (dir' <> "/") ""
  . re "Agda2> " ""
  . re "\\\\n" " "
  where
    re = Utils.replace . Utils.mkRegex  -- apply a regexp
    dir' = T.pack dir
    parentDir' = T.pack (dropFileName dir)

-- | Given an path to an agda file, X.agda,
--  * Reads and expands the script X.in
--  * Runs an interaction session with that stdin
--  * and compares it to X.out
mkSimpleTest :: FilePath -> TestTree
mkSimpleTest agdaFile =
    Tasty.goldenTestIO1
      (takeBaseName agdaFile)
      (readFileMaybeText (agdaFile -<.> "out"))
      runTest
      (textDiffWithTouch agdaFile)
      (pure . Tasty.ShowText)
      (Just $ writeTextFile (agdaFile -<.> "out"))
  where
    runTest = do
      cwd <- getCurrentDirectory
      rawStdin <- T.readFile (agdaFile -<.> "in")
      agdaStdin <- expandInScript (cwd </> agdaFile) rawStdin
      extraArgs <- readFileMaybeText (agdaFile -<.> "flags")

      let agdaArgs =
            "-v0" :
            "-i" : "." :
            "-i" : ".." :
            "--interaction" :
            "--ignore-interfaces" :
            "--no-default-libraries" :
            "--color=never" : -- Highlighting not portable, depends on filepath lengths
            (words . T.unpack . fromMaybe "" $ extraArgs)

      (e, stdout, _) <- readAgdaProcessWithCWD Nothing (Just testDir) agdaArgs agdaStdin
      pure $ filterOutput (cwd </> testDir) stdout

-- | Run @agda --build-library@ for each of the test directories.

{-# OPTIONS_GHC -Wunused-imports #-}

module BuildSucceed.Tests where

import           Data.Maybe                 ( isJust )

import           System.Directory           ( doesFileExist )
import           System.FilePath            ( (</>), (<.>), takeFileName )
import qualified System.FilePath.Find       as Find
import           System.IO.Temp             ( withSystemTempDirectory )

import           Test.Tasty
import           Test.Tasty.Silver.Advanced ( goldenTestIO1, GShow (..) )

import           Succeed.Tests              ( TestResult(..), printTestResult )
import           Utils

testDir :: FilePath
testDir = "test" </> "BuildSucceed"

tests :: IO TestTree
tests = do
  -- Get immediate subdirectories of @testDir@.
  dirs <- drop 1 <$>  -- The first in list is @testDir@ itself.
    Find.find (Find.depth Find.<? 1) (Find.fileType Find.==? Find.Directory) testDir

  let tests = map mkBuildSucceedTest dirs
  return $ testGroup "BuildSucceed" tests

mkBuildSucceedTest ::
     FilePath -- ^ Directory hosting an Agda library.
  -> TestTree
mkBuildSucceedTest dir =
  goldenTestIO1
    testName
    readGolden
    (printTestResult <$> doRun)
    (textDiffWithTouch dir)
    (return . ShowText)
    updGolden
  where
  testName = takeFileName dir
  varFile  = ".." </> testName <.> "vars"
  flagFile = ".." </> testName <.> "flags"
  warnFile = dir <.> "warn"

  -- Unless we have a .warn file, we don't really have a golden
  -- file. Just use a dummy update function.
  -- TODO extend tasty-silver to handle this use case properly
  readGolden = do
    warnExists <- doesFileExist warnFile
    if warnExists then readTextFileMaybe warnFile
                  else return $ Just $ printTestResult TestSuccess

  updGolden = Just $ writeTextFile warnFile

  doRun = withSystemTempDirectory testName \ compDir -> do

    let
      agdaArgs =
        [ "--build-library"
        , "-v0"
        , "-vimpossible:10" -- BEWARE: no spaces allowed here
        , "-vwarning:1"
        , "--double-check"
        , "--ghc-flag=-outputdir=" ++ compDir
        -- , "-vcompile.cmd:1"
        , "--ignore-interfaces"
        , "--vim"
        ]

    (res, ret) <- runAgdaWithCWD testName (Just dir) agdaArgs (Just flagFile) (Just varFile)

    case ret of
      AgdaSuccess warn -> do
        warnExists <- doesFileExist warnFile
        return $
          if warnExists || isJust warn
          then TestSuccessWithWarnings $ stdOut res -- TODO: distinguish log vs. warn?
          else TestSuccess
      AgdaFailure{} -> return $ TestUnexpectedFail res

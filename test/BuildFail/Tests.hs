-- | Run @agda --build-library@ for each of the test directories.

{-# OPTIONS_GHC -Wunused-imports #-}

module BuildFail.Tests where

import           System.FilePath            ( (</>), (<.>), takeFileName )
import qualified System.FilePath.Find       as Find
import           System.IO.Temp             ( withSystemTempDirectory )

import           Test.Tasty
import           Test.Tasty.Silver.Advanced ( goldenTestIO1, GShow (..) )

import           Fail.Tests                 ( expectFail, printTestResult )
import           Utils

testDir :: FilePath
testDir = "test" </> "BuildFail"

tests :: IO TestTree
tests = do
  -- Get immediate subdirectories of @testDir@.
  dirs <- drop 1 <$>  -- The first in list is @testDir@ itself.
    Find.find (Find.depth Find.<? 1) (Find.fileType Find.==? Find.Directory) testDir

  let tests = map mkBuildFailTest dirs
  return $ testGroup "BuildFail" tests

mkBuildFailTest ::
     FilePath -- ^ Directory hosting an Agda library.
  -> TestTree
mkBuildFailTest dir =
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
  errFile  = dir <.> "err"

  readGolden = readTextFileMaybe errFile
  updGolden = Just $ writeTextFile errFile

  doRun = withSystemTempDirectory testName \ compDir -> do

    let
      agdaArgs =
        [ "--build-library"
        , "-vimpossible:10" -- BEWARE: no spaces allowed here
        , "-vwarning:1"
        , "--double-check"
        , "--ghc-flag=-outputdir=" ++ compDir
        -- , "-vcompile.cmd:1"
        , "--ignore-interfaces"
        , "--vim"
        ]

    expectFail <$> do
      -- Andreas, 2025-06-01, AIM XL
      -- @withCurrentDir dir@ does not work correctly here (for reasons beyond my comprehension),
      -- so we set the cwd when calling agda.
      runAgdaWithCWD testName (Just dir) agdaArgs (Just flagFile) (Just varFile)

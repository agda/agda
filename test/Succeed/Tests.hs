{-# LANGUAGE DoAndIfThenElse   #-}

module Succeed.Tests where

import qualified Data.List as List
import Data.Maybe (isJust, fromMaybe)
import Data.Monoid ((<>))
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Text.Encoding

import Test.Tasty
import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced
  (readFileMaybe, goldenTestIO1, GDiff (..), GShow (..))
import Test.Tasty.Silver.Filter ( RegexFilter( RFInclude ) )

import System.Directory
import System.Exit
import System.FilePath
import System.IO.Temp

import Utils

testDir :: FilePath
testDir = "test" </> "Succeed"

tests :: IO TestTree
tests = do
  inpFiles <- reorder <$> getAgdaFilesInDir Rec testDir

  let extraOpts = [ "--ignore-interfaces" , "--vim" ]
  let tests' = map (mkSucceedTest extraOpts testDir) inpFiles

  return $ testGroup "Succeed" tests'
  where
  reorder = id
  -- -- Andreas, 2020-10-19, work around issue #4940:
  -- -- Put @ExecAgda@ last.
  -- reorder = uncurry (++) . List.partition (not . ("ExecAgda" `List.isInfixOf`))

-- | Filtering out succed-tests that require Agda built with -fdebug.

fdebugTestFilter :: [RegexFilter]
fdebugTestFilter =
-- This list was crafted using
--    grep -RP '(?<!-- ){-# OPTIONS.* -v' | grep Succeed/
--  and screening the results (e.g. for comments)
  [ disable "Succeed/Issue1809"
  , disable "Succeed/Issue5730"
  , disable "Succeed/Issue1701II"
  , disable "Succeed/Issue1407"
  , disable "Succeed/ForcedConstructorPattern"
  , disable "Succeed/Issue2292"
  , disable "Succeed/Issue4016"
  , disable "Succeed/Issue2434"
  , disable "Succeed/NotProjectionLike"
  , disable "Succeed/Issue5989"
  , disable "Succeed/Issue2717"
  , disable "Succeed/Issue7286"
  , disable "Succeed/Issue778b"
  , disable "Succeed/Issue1597/Main2"
  , disable "Succeed/RepeatedCase"
  , disable "Succeed/Issue6298-d"
  , disable "Succeed/Issue1770"
  , disable "Succeed/Issue578"
  , disable "Succeed/Issue2300"
  , disable "Succeed/Issue882a"
  , disable "Succeed/Issue1009"
  , disable "Succeed/Issue3933"
  , disable "Succeed/Issue3933"
  , disable "Succeed/Issue5506"
  , disable "Succeed/Issue1595"
  , disable "Succeed/Issue365"
  , disable "Succeed/Issue1914"
  , disable "Succeed/Issue2257b"
  , disable "Succeed/Issue1344"
  , disable "Succeed/Issue4148"
  , disable "Succeed/CheckIApplyConfluenceOnlyWhenCubical"
  , disable "Succeed/OpaqueImport/C"
  , disable "Succeed/OpaqueImport/B"
  , disable "Succeed/OpaqueImport/A"
  , disable "Succeed/Issue2223-constraints-in-frontmatter"
  , disable "Succeed/Issue4211"
  , disable "Succeed/Issue4211"
  , disable "Succeed/Issue3971"
  , disable "Succeed/Issue1740"
  , disable "Succeed/Issue4020"
  ]
  where disable = RFInclude

-- | Tests that get special preparation from the Makefile.
makefileDependentTests :: [RegexFilter]
makefileDependentTests =
  [ disable "Succeed/ExecAgda"
  ]
  where disable = RFInclude

data TestResult
  = TestSuccess
  | TestSuccessWithWarnings T.Text -- the cleaned stdout
  | TestUnexpectedFail ProgramResult
  | TestWrongDotOutput T.Text

mkSucceedTest
  :: AgdaArgs -- ^ Extra options to Agda.
  -> FilePath -- ^ Test directory.
  -> FilePath -- ^ Input file (an Agda file).
  -> TestTree
mkSucceedTest extraOpts dir agdaFile =
  goldenTestIO1
    testName
    readGolden
    (printTestResult <$> doRun)
    (textDiffWithTouch agdaFile)
    (return . ShowText)
    updGolden
  where
  testName = asTestName dir agdaFile
  baseName = dropAgdaExtension agdaFile
  varFile  = baseName <.> "vars"
  flagFile = baseName <.> "flags"
  warnFile = baseName <.> "warn"

  -- Unless we have a .warn file, we don't really have a golden
  -- file. Just use a dummy update function.
  -- TODO extend tasty-silver to handle this use case properly
  readGolden = do
    warnExists <- doesFileExist warnFile
    if warnExists then readTextFileMaybe warnFile
                  else return $ Just $ printTestResult TestSuccess

  updGolden = Just $ writeTextFile warnFile

  doRun = withSystemTempDirectory testName \ compDir -> do

    let agdaArgs = [ "-v0", "-i" ++ dir, "-itest/", agdaFile
                   , "-vimpossible:10" -- BEWARE: no spaces allowed here
                   , "-vwarning:1"
                   , "--double-check"
                   , "--ghc-flag=-outputdir=" ++ compDir
                   -- , "-vcompile.cmd:1"
                   ] ++
                   [ if testName == "Issue481"
                     then "--no-default-libraries"
                     else "--no-libraries"
                   ] ++
                   extraOpts

    (res, ret) <- runAgdaWithOptions testName agdaArgs (Just flagFile) (Just varFile)

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
      AgdaFailure{} -> return $ TestUnexpectedFail res

printTestResult :: TestResult -> T.Text
printTestResult = \case
  TestSuccess               -> "AGDA_SUCCESS\n\n"
  TestSuccessWithWarnings t -> t
  TestUnexpectedFail p      -> "AGDA_UNEXPECTED_FAIL\n\n" <> printProgramResult p
  TestWrongDotOutput t      -> "AGDA_WRONG_DOT_OUTPUT\n\n" <> t

-- WAS: List of test cases that do not pass the --double-check yet
-- NOTE
--  Why are a lot of the sized types tests not working with --double-check? The reason can be found
--  in Agda.TypeChecking.MetaVars.blockTermOnProblem, which does not block a term on unsolved size
--  constraints (introduced by @andreasabel in 3be79cc7fd). This might be safe to do, but it will
--  not be accepted by a double check.
--
-- Andreas, 2021-04-29, issue #5352
-- Now, there is an option `--no-double-check` in the respective .flags file.
-- To get the list, try:  grep no-double-check *.flags

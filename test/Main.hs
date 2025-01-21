module Main where

import           Control.Monad                  (when)
import qualified Data.Text                      as T

import           System.Environment             (getEnvironment)
import           System.Exit                    (exitFailure)

import           Test.Tasty                     as T
import           Test.Tasty.Silver.Interactive  as TM
import           Test.Tasty.Silver.Filter       (RegexFilter)

import qualified Bugs.Tests
import qualified Compiler.Tests
import qualified CubicalSucceed.Tests
import qualified Fail.Tests
import qualified Interactive.Tests
import qualified Internal.Tests
import qualified LaTeXAndHTML.Tests
import qualified LibSucceed.Tests
import qualified Succeed.Tests
import qualified UserManual.Tests

import           Utils

main :: IO ()
main = do
  -- Detect properties of Agda build
  agdaBin <- getAgdaBin <$> getEnvironment
  agdaBinExists <- doesCommandExist agdaBin
  builtWithMakefile <- doesEnvContain "AGDA_BIN"
  builtWithFDebug <- wasAgdaCompiledWithFDebug
  -- Warn/err about un-recommended builds
  when (not agdaBinExists) do
      putStrLn $ unwords ["Could not find executable", agdaBin ]
      exitFailure
  when (not builtWithMakefile) do
    putStrLn $ unlines
      [ "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@"
      , "@ The AGDA_BIN environment variable is not set.                             @"
      , "@ Maybe you are running 'cabal test' or 'cabal v1-install --runtests'?      @"
      , "@ This will only run parts of the Agda test-suite.                          @"
      , "@ The preferred way of running the tests is via the Makefile ('make test'). @"
      , "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@"
      ]
  when (not builtWithFDebug) do
    putStrLn $ unlines
      [ "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@"
      , "@ Detected an Agda built without the '-fdebug' cabal flag,                  @"
      , "@ tests that rely on debugging output will be skipped.                      @"
      , "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@"
      ]
  -- Calcualte tests to disable
  let disabledTests = concat
        [ if not builtWithFDebug   then fdebugTestFilter       else []
        , if not builtWithMakefile then testsWithSystemDeps    else []
        , if not builtWithMakefile then makefileDependentTests else []
        , alwaysDisabledTests
        ]
  -- Run tests
  TM.defaultMain1 disabledTests =<< allTests

-- | All tests covered by the tasty testsuite.
allTests :: IO TestTree
allTests = do
  testGroup "all" {- . concat -} <$> do
    sequence $
      -- N.B.: This list is written using (:) so that lines can be swapped easily:
      -- (The number denotes the order of the Makefile as of 2021-08-25.)
      {- 1 -} sg Succeed.Tests.tests        :
      {- 2 -} sg Fail.Tests.tests           :
      {- 3 -} sg Bugs.Tests.tests           :
      {- 4 -} pu Interactive.Tests.tests    :
      {- 9 -} sg UserManual.Tests.tests     :
      {- 5 -} sg LaTeXAndHTML.Tests.tests   :
      {- 6 -} pu Internal.Tests.tests       :
      {- 7 -} sg Compiler.Tests.tests       :
      {- 8 -} sg LibSucceed.Tests.tests     :
      {- 9 -} sg CubicalSucceed.Tests.tests :
      []
  where
  sg = id
  pu = pure
  -- If one @tests@ returns a list of test trees, use these wrappers:
  -- sg m = (:[]) <$> m
  -- pu x = pure [x]

-- | Tests that require Agda built with -fdebug.

fdebugTestFilter :: [RegexFilter]
fdebugTestFilter = concat
  [ Succeed.Tests.fdebugTestFilter
  , Fail.Tests.fdebugTestFilter
  , Compiler.Tests.fdebugTestFilter
  ]

-- | Tests with system dependencies
-- (note that this list is not complete:
--  some tests include ad-hoc checks, e.g. for NodeJS)

testsWithSystemDeps :: [RegexFilter]
testsWithSystemDeps = concat
  [ LaTeXAndHTML.Tests.latexTests
  , LaTeXAndHTML.Tests.icuTests
  , Compiler.Tests.stdlibTestFilter
  ]

-- | Some tests get extra setup through the @Makefile@.

makefileDependentTests :: [RegexFilter]
makefileDependentTests = Succeed.Tests.makefileDependentTests

-- | Tests that are always disabled
alwaysDisabledTests :: [RegexFilter]
alwaysDisabledTests = concat
  [ Compiler.Tests.disabledTests
  , LibSucceed.Tests.disabledTests
  , LaTeXAndHTML.Tests.disabledTests
  ]

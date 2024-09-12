module Main where

import qualified Compiler.Tests as COMPILER
import qualified Succeed.Tests as SUCCEED
import qualified Fail.Tests as FAIL
import qualified Interactive.Tests as INTERACTIVE
import qualified Internal.Tests as INTERNAL
import qualified LaTeXAndHTML.Tests as LATEXHTML
import qualified LibSucceed.Tests as LIBSUCCEED
import qualified CubicalSucceed.Tests as CUBICALSUCCEED
import qualified UserManual.Tests as USERMANUAL
import qualified Bugs.Tests as BUGS

import Test.Tasty as T
import Test.Tasty.Silver.Interactive as TM
import Test.Tasty.Silver.Filter (RegexFilter)

import System.Environment (getEnvironment)
import System.Exit

import Utils
import Control.Monad (when)
import qualified Data.Text as T

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
      {- 1 -} sg SUCCEED.tests     :
      {- 2 -} sg FAIL.tests        :
      {- 3 -} sg BUGS.tests        :
      {- 4 -} pu INTERACTIVE.tests :
      {- 9 -} sg USERMANUAL.tests  :
      {- 5 -} sg LATEXHTML.tests   :
      {- 6 -} pu INTERNAL.tests    :
      {- 7 -} sg COMPILER.tests    :
      {- 8 -} sg LIBSUCCEED.tests  :
      {- 9 -} sg CUBICALSUCCEED.tests  :
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
  [   SUCCEED.fdebugTestFilter
  ,   FAIL.fdebugTestFilter
  ,   COMPILER.fdebugTestFilter
  ,   INTERACTIVE.fdebugTestFilter
  ]

-- | Tests with system dependencies
-- (note that this list is not complete:
--  some tests include ad-hoc checks, e.g. for NodeJS)

testsWithSystemDeps :: [RegexFilter]
testsWithSystemDeps = concat
  [ LATEXHTML.latexTests
  , LATEXHTML.icuTests
  , COMPILER.stdlibTestFilter
  ]

-- | Some tests get extra setup through the @Makefile@.

makefileDependentTests :: [RegexFilter]
makefileDependentTests = SUCCEED.makefileDependentTests

-- | Tests that are always disabled
alwaysDisabledTests :: [RegexFilter]
alwaysDisabledTests = concat
  [ COMPILER.disabledTests
  , LIBSUCCEED.disabledTests
  , LATEXHTML.disabledTests
  ]

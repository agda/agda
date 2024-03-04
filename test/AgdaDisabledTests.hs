
-- | Lists of disabled tests
-- & related helper functions

module AgdaDisabledTests where

import qualified Compiler.Tests as COMPILER
import qualified Succeed.Tests as SUCCEED
import qualified LaTeXAndHTML.Tests as LATEXHTML
import qualified LibSucceed.Tests as LIBSUCCEED

import qualified Test.Tasty.Silver.Interactive as TM
import Test.Tasty (TestTree)
import Test.Tasty.Silver.Filter (RegexFilter)
import Utils (doesEnvContain, doesCommandExist, getAgdaBin)
import System.Environment (getEnvironment)
import System.Exit ( exitFailure )

-- | Helper to make a @cabal test@-runnable test suite
-- that avoids the known-broken tests
runTests :: TestTree -> IO ()
runTests tests = do
  doesEnvContain "AGDA_BIN" >>= \case
    True  -> TM.defaultMain1 disabledTests tests
    False -> do
      putStrLn $ unlines
        [ "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@"
        , "@ The AGDA_BIN environment variable is not set.                             @"
        , "@ Maybe you are running 'cabal test' or 'cabal v1-install --runtests'?      @"
        , "@ This will only run parts of the Agda test-suite.                          @"
        , "@ The preferred way of running the tests is via the Makefile ('make test'). @"
        , "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@"
        ]
      agdaBin <- getAgdaBin <$> getEnvironment
      doesCommandExist agdaBin >>= \case
        True ->
          TM.defaultMain1 cabalDisabledTests tests
        False -> do
          putStrLn $ unwords ["Could not find executable", agdaBin ]
          exitFailure

-- | Tests not yet runnable by @cabal test@.
cabalDisabledTests :: [RegexFilter]
cabalDisabledTests = concat
  [ disabledTests
  , makefileDependentTests
  , LATEXHTML.latexTests
  , LATEXHTML.icuTests
  , COMPILER.stdlibTestFilter
  ]

-- | Tests that need @Makefile@ setup to run
makefileDependentTests :: [RegexFilter]
makefileDependentTests = SUCCEED.makefileDependentTests

-- | Tests not runnable at all, for other reasons
disabledTests :: [RegexFilter]
disabledTests = concat
  [ COMPILER.disabledTests
  , LIBSUCCEED.disabledTests
  , LATEXHTML.disabledTests
  ]

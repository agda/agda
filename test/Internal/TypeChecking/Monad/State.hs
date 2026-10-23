module Internal.TypeChecking.Monad.State ( tests ) where

import Control.Monad.Except (throwError)
import Data.HashMap.Strict qualified as HMap
import Data.Monoid (Sum(..))
import System.Directory (getCurrentDirectory)

import Agda.Syntax.Internal (alwaysUnblock)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.State (localTCState)
import Agda.TypeChecking.Monad.Statistics (tick)
import Agda.Utils.FileName (mkAbsolute)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit

run :: TCM a -> IO a
run action = do
  root <- mkAbsolute <$> getCurrentDirectory
  state <- initState root
  fst <$> runTCM initEnv state action

tests :: TestTree
tests = testGroup "Internal.TypeChecking.Monad.State"
  [ testCase "restores state on pattern violation" do
      result <- run do
        setTCLens stFreshInt 7
        catchPatternErr (\_ -> (,) <$> useTC stFreshInt <*> useTC stPostponeInstanceSearch) $
          localTCState do
            setTCLens stFreshInt 17
            setTCLens stPostponeInstanceSearch True
            patternViolation alwaysUnblock
      result @?= (7, False)

  , testCase "restores state on error" do
      result <- run do
        setTCLens stFreshInt 7
        catchError_ (localTCState do
          setTCLens stFreshInt 17
          throwError (GenericException "expected")) \case
            GenericException "expected" -> useTC stFreshInt
            err -> throwError err
      result @?= 7

  , testCase "keeps statistics on failure" do
      result <- run do
        setTCLens stFreshInt 7
        catchPatternErr (const $ pure ()) $ localTCState do
          setTCLens stFreshInt 17
          tick "failed speculation"
          patternViolation alwaysUnblock
        fresh <- useTC stFreshInt
        ticks <- HMap.lookup "failed speculation" . statTicks
                   <$> useTC stStatistics
        pure (fresh, ticks)
      result @?= (7, Just (Sum 1))
  ]

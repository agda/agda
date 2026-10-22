module Internal.TypeChecking.Monad.State ( tests ) where

import Control.Monad.Except (throwError)
import Data.HashMap.Strict qualified as HMap
import Data.Monoid (Sum(..))

import Agda.Syntax.Internal (alwaysUnblock)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.State (localTCState, localTCStateSaving)
import Agda.TypeChecking.Monad.Statistics (tick)
import Agda.Utils.FileName (mkAbsolute)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

run :: TCM a -> IO a
run action = do
  state <- initState (mkAbsolute "/")
  fst <$> runTCM initEnv state action

tests :: TestTree
tests = testGroup "Internal.TypeChecking.Monad.State"
  [ testProperty "successful speculation restores state and returns its result" $
      \(outer :: Int) (inner :: Int) -> ioProperty $ run do
        setTCLens stFreshInt outer
        result <- localTCState do
          setTCLens stFreshInt inner
          useTC stFreshInt
        restored <- useTC stFreshInt
        pure (result == inner && restored == outer)

  , testCase "pattern violations restore speculative state before the handler" do
      result <- run do
        setTCLens stFreshInt 7
        catchPatternErr (\_ -> (,) <$> useTC stFreshInt <*> useTC stPostponeInstanceSearch) $
          localTCState do
            setTCLens stFreshInt 17
            setTCLens stPostponeInstanceSearch True
            patternViolation alwaysUnblock
      result @?= (7, False)

  , testCase "ordinary errors restore state with a state-preserving handler" do
      result <- run do
        setTCLens stFreshInt 7
        catchError_ (localTCState do
          setTCLens stFreshInt 17
          throwError (GenericException "expected")) \case
            GenericException "expected" -> useTC stFreshInt
            err -> throwError err
      result @?= 7

  , testCase "failed speculation restores state but preserves statistics" do
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

  , testCase "nested speculation restores the enclosing state" do
      result <- run do
        setTCLens stFreshInt 7
        inside <- localTCState do
          setTCLens stFreshInt 11
          catchPatternErr (const $ useTC stFreshInt) $ localTCState do
            setTCLens stFreshInt 17
            patternViolation alwaysUnblock
        outside <- useTC stFreshInt
        pure (inside, outside)
      result @?= (11, 7)

  , testCase "saving speculation returns the inner state and restores the outer state" do
      result <- run do
        setTCLens stFreshInt 7
        (value, saved) <- localTCStateSaving do
          setTCLens stFreshInt 11
          pure (13 :: Int)
        restored <- useTC stFreshInt
        pure (value, saved ^. stFreshInt, restored)
      result @?= (13, 11, 7)
  ]

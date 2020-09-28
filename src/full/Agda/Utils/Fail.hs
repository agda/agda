-- | A pure MonadFail.
module Agda.Utils.Fail where

-- Control.Monad.Fail import is redundant since GHC 8.8.1
import Control.Monad.Fail

newtype Fail a = Fail { runFail :: Either String a }
  deriving (Functor, Applicative, Monad)

instance MonadFail Fail where
  fail = Fail . Left

runFail_ :: Fail a -> a
runFail_ = either error id . runFail

-- | A pure MonadFail.
module Agda.Utils.Fail where

newtype Fail a = Fail { runFail :: Either String a }
  deriving (Functor, Applicative, Monad)

instance MonadFail Fail where
  fail = Fail . Left

runFail_ :: Fail a -> a
runFail_ = either error id . runFail

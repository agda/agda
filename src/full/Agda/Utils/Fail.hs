-- | A pure MonadFail.
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Agda.Utils.Fail where

-- redundant import with GHC 8.8.2
import Control.Monad.Fail

newtype Fail a = Fail { runFail :: Either String a }
  deriving (Functor, Applicative, Monad)

instance MonadFail Fail where
  fail = Fail . Left

runFail_ :: Fail a -> a
runFail_ = either error id . runFail


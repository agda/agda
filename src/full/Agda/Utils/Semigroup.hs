-- | Some semigroup instances used in several places

module Agda.Utils.Semigroup (
  module Data.Semigroup)
where

import Data.Semigroup ( Semigroup, (<>) )

import Control.Applicative (liftA2)

import Control.Monad.Reader (ReaderT)
import Control.Monad.State  (StateT)

instance (Applicative m, Semigroup doc) => Semigroup (ReaderT s m doc) where
  {-# INLINE (<>) #-}
  (<>) = liftA2 (<>)

instance (Monad m, Semigroup doc)       => Semigroup (StateT s m doc)  where
  {-# INLINE (<>) #-}
  (<>) = liftA2 (<>)

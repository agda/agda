{-# OPTIONS -cpp #-}

module Utils.Maybe
    ( module Utils.Maybe
    , module Data.Maybe
    ) where

import Data.Monoid
import Data.Maybe

fromMaybeM :: Monad m => m a -> m (Maybe a) -> m a
fromMaybeM m mm = maybe m return =<< mm


{-# OPTIONS -cpp #-}

module Utils.Maybe
    ( module Utils.Maybe
    , module Data.Maybe
    ) where

import Data.Monoid
import Data.Maybe

instance Monoid (Maybe a) where
    mempty		= Nothing
    mappend (Just x) _	= Just x
    mappend Nothing m	= m

fromMaybeM :: Monad m => m a -> m (Maybe a) -> m a
fromMaybeM m mm = maybe m return =<< mm


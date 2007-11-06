{-# OPTIONS -cpp #-}

module Utils.Maybe
    ( module Utils.Maybe
    , module Data.Maybe
    ) where

import Data.Monoid
import Data.Maybe

#if __GLASGOW_HASKELL__ < 608
-- We should really check for the version of base here.
instance Monoid (Maybe a) where
    mempty		= Nothing
    mappend (Just x) _	= Just x
    mappend Nothing m	= m
#endif

fromMaybeM :: Monad m => m a -> m (Maybe a) -> m a
fromMaybeM m mm = maybe m return =<< mm


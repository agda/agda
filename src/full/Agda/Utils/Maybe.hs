{-# LANGUAGE CPP #-}

module Agda.Utils.Maybe
    ( module Agda.Utils.Maybe
    , module Data.Maybe
    ) where

import Data.Monoid
import Data.Maybe

fromMaybeM :: Monad m => m a -> m (Maybe a) -> m a
fromMaybeM m mm = maybe m return =<< mm

unzipMaybe :: Maybe (a,b) -> (Maybe a, Maybe b)
unzipMaybe Nothing      = (Nothing, Nothing)
unzipMaybe (Just (a,b)) = (Just a, Just b)

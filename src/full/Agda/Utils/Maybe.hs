{-# LANGUAGE CPP #-}

module Agda.Utils.Maybe
    ( module Agda.Utils.Maybe
    , module Data.Maybe
    ) where

-- import Data.Monoid
import Data.Maybe

maybeM :: Monad m => m b -> (a -> m b) -> m (Maybe a) -> m b
maybeM n j mm = maybe n j =<< mm

fromMaybeM :: Monad m => m a -> m (Maybe a) -> m a
fromMaybeM m mm = maybeM m return mm

unzipMaybe :: Maybe (a,b) -> (Maybe a, Maybe b)
unzipMaybe Nothing      = (Nothing, Nothing)
unzipMaybe (Just (a,b)) = (Just a, Just b)

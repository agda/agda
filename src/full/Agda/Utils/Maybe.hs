{-# LANGUAGE CPP #-}

module Agda.Utils.Maybe
    ( module Agda.Utils.Maybe
    , module Data.Maybe
    ) where

import Data.Monoid
import Data.Maybe

fromMaybeM :: Monad m => m a -> m (Maybe a) -> m a
fromMaybeM m mm = maybe m return =<< mm

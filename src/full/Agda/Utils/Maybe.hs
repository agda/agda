{-# LANGUAGE CPP #-}

module Agda.Utils.Maybe
    ( module Agda.Utils.Maybe
    , module Data.Maybe
    ) where

import Data.Maybe

maybeM :: Monad m => m b -> (a -> m b) -> m (Maybe a) -> m b
maybeM n j mm = maybe n j =<< mm

fromMaybeM :: Monad m => m a -> m (Maybe a) -> m a
fromMaybeM m mm = maybeM m return mm

unzipMaybe :: Maybe (a,b) -> (Maybe a, Maybe b)
unzipMaybe Nothing      = (Nothing, Nothing)
unzipMaybe (Just (a,b)) = (Just a, Just b)

forMaybe :: [a] -> (a -> Maybe b) -> [b]
forMaybe = flip mapMaybe

-- | Version of 'maybe' with different argument ordering.
--   Often, we want to case on a 'Maybe', do something interesting
--   in the 'Just' case, but only a default action in the 'Nothing'
--   case.  Then, the argument ordering of @caseMaybe@ is preferable.
--
--   @caseMaybe m err f = flip (maybe err) m f@
caseMaybe :: Maybe a -> b -> (a -> b) -> b
caseMaybe m err f = maybe err f m

-- | Monadic version of 'caseMaybe'.
--   That is, 'maybeM' with a different argument ordering.
caseMaybeM :: Monad m => m (Maybe a) -> m b -> (a -> m b) -> m b
caseMaybeM mm err f = maybeM  err f mm

-- | 'caseMaybeM' with flipped branches.
ifJustM :: Monad m => m (Maybe a) -> (a -> m b) -> m b -> m b
ifJustM mm = flip (caseMaybeM mm)

-- | A more telling name for 'Traversable.forM' for the 'Maybe' collection type.
--   Or: 'caseMaybe' without the 'Nothing' case.
whenJust :: Monad m => Maybe a -> (a -> m ()) -> m ()
whenJust m k = caseMaybe m (return ()) k

-- | 'caseMaybeM' without the 'Nothing' case.
whenJustM :: Monad m => m (Maybe a) -> (a -> m ()) -> m ()
whenJustM c m = c >>= (`whenJust` m)

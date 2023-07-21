{-# OPTIONS_GHC -Wunused-imports #-}

-- | Extend 'Data.Maybe' by common operations for the 'Maybe' type.
--
--   Note: since this module is usually imported unqualified,
--   we do not use short names, but all names contain 'Maybe',
--   'Just', or 'Nothing.

module Agda.Utils.Maybe
    ( module Agda.Utils.Maybe
    , module Data.Maybe
    ) where

import Control.Applicative
import Control.Monad.Trans.Maybe

import Data.Maybe

-- * Conversion.

-- | Retain object when tag is 'True'.
boolToMaybe :: Bool -> a -> Maybe a
boolToMaybe b x = if b then Just x else Nothing

-- * Collection operations.

-- | @unionWith@ for collections of size <= 1.
unionMaybeWith :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
unionMaybeWith f Nothing mb      = mb
unionMaybeWith f ma      Nothing = ma
unionMaybeWith f (Just a) (Just b) = Just $ f a b

-- | @unionsWith@ for collections of size <= 1.
unionsMaybeWith :: (a -> a -> a) -> [Maybe a] -> Maybe a
unionsMaybeWith f ms = case catMaybes ms of
  [] -> Nothing
  as -> Just $ foldl1 f as

-- | Unzipping a list of length <= 1.

unzipMaybe :: Maybe (a,b) -> (Maybe a, Maybe b)
unzipMaybe Nothing      = (Nothing, Nothing)
unzipMaybe (Just (a,b)) = (Just a, Just b)

-- | Filtering a singleton list.
--
--   @filterMaybe p a = 'listToMaybe' ('filter' p [a])@

filterMaybe :: (a -> Bool) -> a -> Maybe a
filterMaybe p a
  | p a       = Just a
  | otherwise = Nothing

-- * Conditionals and loops.

-- | Version of 'mapMaybe' with different argument ordering.

forMaybe :: [a] -> (a -> Maybe b) -> [b]
forMaybe = flip mapMaybe

-- | Version of 'maybe' with different argument ordering.
--   Often, we want to case on a 'Maybe', do something interesting
--   in the 'Just' case, but only a default action in the 'Nothing'
--   case.  Then, the argument ordering of @caseMaybe@ is preferable.
--
--   @caseMaybe m d f = flip (maybe d) m f@
caseMaybe :: Maybe a -> b -> (a -> b) -> b
caseMaybe m d f = maybe d f m

-- | 'caseMaybe' with flipped branches.
ifJust :: Maybe a -> (a -> b) -> b -> b
ifJust m f d = maybe d f m

-- * Monads and Maybe.

-- | Monadic version of 'maybe'.

maybeM :: Monad m => m b -> (a -> m b) -> m (Maybe a) -> m b
maybeM n j mm = maybe n j =<< mm

-- | Monadic version of 'fromMaybe'.

fromMaybeM :: Monad m => m a -> m (Maybe a) -> m a
fromMaybeM m mm = maybeM m return mm

-- | Monadic version of 'caseMaybe'.
--   That is, 'maybeM' with a different argument ordering.
caseMaybeM :: Monad m => m (Maybe a) -> m b -> (a -> m b) -> m b
caseMaybeM mm d f = maybeM d f mm

-- | 'caseMaybeM' with flipped branches.
ifJustM :: Monad m => m (Maybe a) -> (a -> m b) -> m b -> m b
ifJustM mm = flip (caseMaybeM mm)

-- | A more telling name for 'Traversable.forM_' for the 'Maybe' collection type.
--   Or: 'caseMaybe' without the 'Nothing' case.
whenJust :: Monad m => Maybe a -> (a -> m ()) -> m ()
whenJust m k = caseMaybe m (return ()) k

-- | 'caseMaybe' without the 'Just' case.
whenNothing :: Monoid m => Maybe a -> m -> m
whenNothing m d = caseMaybe m d (\_ -> mempty)

-- | 'caseMaybeM' without the 'Nothing' case.
whenJustM :: Monad m => m (Maybe a) -> (a -> m ()) -> m ()
whenJustM c m = c >>= (`whenJust` m)

-- | 'caseMaybeM' without the 'Just' case.
whenNothingM :: Monad m => m (Maybe a) -> m () -> m ()
whenNothingM mm d = maybe d (\_ -> return ()) =<< mm

-- | Lazy version of @allJust <.> sequence@.
--   (@allJust = mapM@ for the @Maybe@ monad.)
--   Only executes monadic effect while @isJust@.
allJustM :: Monad m => [m (Maybe a)] -> m (Maybe [a])
allJustM = runMaybeT . mapM MaybeT

-- | Lift a maybe to an Alternative.
liftMaybe :: Alternative f => Maybe a -> f a
liftMaybe = maybe empty pure

-- | Like 'span', takes the prefix of a list satisfying a predicate.
-- Returns the run of 'Just's until the first 'Nothing', and the tail of
-- the list.
spanMaybe :: (a -> Maybe b) -> [a] -> ([b],[a])
spanMaybe _ [] = ([], [])
spanMaybe p xs@(x:xs') = case p x of
    Just y  -> let (ys, zs) = spanMaybe p xs' in (y : ys, zs)
    Nothing -> ([], xs)

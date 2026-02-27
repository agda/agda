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

import Agda.Utils.Null qualified as Null

-- * Conversion.

-- | Retain object when tag is 'True'.
boolToMaybe :: Bool -> a -> Maybe a
boolToMaybe b x = if b then Just x else Nothing

{-# INLINE predicateToMaybe #-}
-- | Retain object when it passes the given test.
predicateToMaybe :: (a -> Bool) -> a -> Maybe a
predicateToMaybe f = \x -> boolToMaybe (f x) x

-- | Unwrap a 'Maybe' value, returning 'Null.empty' for 'Nothing'.
orEmpty :: Null.Null a => Maybe a -> a
orEmpty Nothing  = Null.empty
orEmpty (Just x) = x

-- * Collection operations.

{-# INLINE unionMaybeWith #-}
-- | @unionWith@ for collections of size <= 1.
unionMaybeWith :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
unionMaybeWith f = \ma mb -> case (ma, mb) of
  (Nothing, mb     ) -> mb
  (ma     , Nothing) -> ma
  (Just a , Just b ) -> Just $ f a b

{-# INLINE unionsMaybeWith #-}
-- | @unionsWith@ for collections of size <= 1.
unionsMaybeWith :: (a -> a -> a) -> [Maybe a] -> Maybe a
unionsMaybeWith f = \ms -> case catMaybes ms of
  [] -> Nothing
  as -> Just $ foldl1 f as

-- | Unzipping a list of length <= 1.

unzipMaybe :: Maybe (a,b) -> (Maybe a, Maybe b)
unzipMaybe Nothing      = (Nothing, Nothing)
unzipMaybe (Just (a,b)) = (Just a, Just b)

{-# INLINE filterMaybe #-}
-- | Filtering a singleton list.
--
--   @filterMaybe p a = 'listToMaybe' ('filter' p [a])@
filterMaybe :: (a -> Bool) -> a -> Maybe a
filterMaybe = \p a -> if p a then Just a else Nothing

-- * Conditionals and loops.

{-# INLINE forMaybe #-}
-- | Version of 'mapMaybe' with different argument ordering.
forMaybe :: [a] -> (a -> Maybe b) -> [b]
forMaybe = flip mapMaybe

{-# INLINE caseMaybe #-}
-- | Version of 'maybe' with different argument ordering.
--   Often, we want to case on a 'Maybe', do something interesting
--   in the 'Just' case, but only a default action in the 'Nothing'
--   case.  Then, the argument ordering of @caseMaybe@ is preferable.
--
--   @caseMaybe m d f = flip (maybe d) m f@
caseMaybe :: Maybe a -> b -> (a -> b) -> b
caseMaybe = \m d f -> maybe d f m

-- | 'caseMaybe' with flipped branches.
ifJust :: Maybe a -> (a -> b) -> b -> b
ifJust = \m f d -> maybe d f m

-- * Monads and Maybe.

{-# INLINE maybeM #-}
-- | Monadic version of 'maybe'.
maybeM :: Monad m => m b -> (a -> m b) -> m (Maybe a) -> m b
maybeM = \n j mm -> maybe n j =<< mm

{-# INLINE fromMaybeM #-}
-- | Monadic version of 'fromMaybe'.
fromMaybeM :: Monad m => m a -> m (Maybe a) -> m a
fromMaybeM = \m mm -> maybeM m return mm

{-# INLINE caseMaybeM #-}
-- | Monadic version of 'caseMaybe'.
--   That is, 'maybeM' with a different argument ordering.
caseMaybeM :: Monad m => m (Maybe a) -> m b -> (a -> m b) -> m b
caseMaybeM = \mm d f -> maybeM d f mm

{-# INLINE ifJustM #-}
-- | 'caseMaybeM' with flipped branches.
ifJustM :: Monad m => m (Maybe a) -> (a -> m b) -> m b -> m b
ifJustM = \mm -> flip (caseMaybeM mm)

{-# INLINE whenJust #-}
-- | A more telling name for 'Traversable.forM_' for the 'Maybe' collection type.
--   Or: 'caseMaybe' without the 'Nothing' case.
whenJust :: Monad m => Maybe a -> (a -> m ()) -> m ()
whenJust = \m k -> caseMaybe m (return ()) k

{-# INLINE whenNothing #-}
-- | Pendent to 'whenJust'.
whenNothing :: Monad m => Maybe a -> m () -> m ()
whenNothing = \m d -> caseMaybe m d \ _ -> return ()

-- -- | 'caseMaybe' without the 'Just' case.
-- whenNothing :: Monoid m => Maybe a -> m -> m
-- whenNothing m d = caseMaybe m d \ _ -> mempty

{-# INLINE whenJustM #-}
-- | 'caseMaybeM' without the 'Nothing' case.
whenJustM :: Monad m => m (Maybe a) -> (a -> m ()) -> m ()
whenJustM = \c m -> c >>= (`whenJust` m)

{-# INLINE whenNothingM #-}
-- | 'caseMaybeM' without the 'Just' case.
whenNothingM :: Monad m => m (Maybe a) -> m () -> m ()
whenNothingM = \mm d -> maybe d (\_ -> return ()) =<< mm

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

-- * MaybeT

-- | Run a 'MaybeT' with a default value for 'Nothing'.
fromMaybeT :: Monad m => a -> MaybeT m a -> m a
fromMaybeT a m = fromMaybe a <$> runMaybeT m

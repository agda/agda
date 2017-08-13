{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}

#if __GLASGOW_HASKELL__ >= 708
{-# LANGUAGE DeriveGeneric #-}
#endif


{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | A strict version of the 'Maybe' type.
--
--   Import qualified, as in
--   @
--     import qualified Agda.Utils.Maybe.Strict as Strict
--   @
--
-- Copyright :  (c) 2006-2007 Roman Leshchinskiy
--              (c) 2013 Simon Meier
-- License   :  BSD-style (see the file LICENSE)
--
-- Copyright :  (c) 2014 Andreas Abel

module Agda.Utils.Maybe.Strict
  ( module Data.Strict.Maybe
  , module Agda.Utils.Maybe.Strict
  ) where

-- The following code is copied from
-- http://hackage.haskell.org/package/strict-base-types-0.3.0/docs/src/Data-Maybe-Strict.html

import           Prelude             hiding (Maybe (..), maybe, null)
import qualified Prelude             as Lazy

import           Control.Applicative (pure, (<$>))
import           Control.DeepSeq     (NFData (..))
import           Data.Binary         (Binary (..))
import           Data.Data           (Data (..))
import           Data.Semigroup      (Semigroup, Monoid, (<>), mempty, mappend)
import           Data.Foldable       (Foldable (..))
import           Data.Traversable    (Traversable (..))
import           Data.Typeable       (Typeable)
import           Data.Strict.Maybe   (Maybe (Nothing, Just), fromJust,
                                      fromMaybe, isJust, isNothing, maybe)
#if __GLASGOW_HASKELL__ >= 708
import           GHC.Generics        (Generic (..))
#endif

import Agda.Utils.Null

toStrict :: Lazy.Maybe a -> Maybe a
toStrict Lazy.Nothing  = Nothing
toStrict (Lazy.Just x) = Just x

toLazy :: Maybe a -> Lazy.Maybe a
toLazy Nothing  = Lazy.Nothing
toLazy (Just x) = Lazy.Just x

deriving instance Data a => Data (Maybe a)
deriving instance Typeable Maybe

#if __GLASGOW_HASKELL__ >= 708
deriving instance Generic  (Maybe a)
#endif

instance Null (Maybe a) where
  empty = Nothing
  null = isNothing

-- The monoid instance was fixed in strict-base-types 0.5.0. See
-- Issue 1805.
instance Semigroup a => Semigroup (Maybe a) where
  Nothing <> m       = m
  m       <> Nothing = m
  Just x1 <> Just x2 = Just (x1 <> x2)

instance Semigroup a => Monoid (Maybe a) where
  mempty  = Nothing
  mappend = (<>)

instance Foldable Maybe where
    foldMap _ Nothing  = mempty
    foldMap f (Just x) = f x

instance Traversable Maybe where
    traverse _ Nothing  = pure Nothing
    traverse f (Just x) = Just <$> f x

instance NFData a => NFData (Maybe a) where
  rnf = rnf . toLazy

instance Binary a => Binary (Maybe a) where
  put = put . toLazy
  get = toStrict <$> get

-- | Analogous to 'Lazy.listToMaybe' in "Data.Maybe".
listToMaybe :: [a] -> Maybe a
listToMaybe []        =  Nothing
listToMaybe (a:_)     =  Just a

-- | Analogous to 'Lazy.maybeToList' in "Data.Maybe".
maybeToList :: Maybe a -> [a]
maybeToList  Nothing   = []
maybeToList  (Just x)  = [x]

-- | Analogous to 'Lazy.catMaybes' in "Data.Maybe".
catMaybes :: [Maybe a] -> [a]
catMaybes ls = [x | Just x <- ls]

-- | Analogous to 'Lazy.mapMaybe' in "Data.Maybe".
mapMaybe :: (a -> Maybe b) -> [a] -> [b]
mapMaybe _ []     = []
mapMaybe f (x:xs) = case f x of
    Nothing -> rs
    Just r  -> r:rs
  where
    rs = mapMaybe f xs

-- The remaining code is a copy of Agda.Utils.Maybe

-- * Collection operations.

-- | @unionWith@ for collections of size <= 1.
unionMaybeWith :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
unionMaybeWith f Nothing mb      = mb
unionMaybeWith f ma      Nothing = ma
unionMaybeWith f (Just a) (Just b) = Just $ f a b

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
--   @caseMaybe m err f = flip (maybe err) m f@
caseMaybe :: Maybe a -> b -> (a -> b) -> b
caseMaybe m err f = maybe err f m

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

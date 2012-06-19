{-# LANGUAGE DeriveFoldable #-}
-- {-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveTraversable #-}

-- | Lists without duplicates.
--
--   Note: use only for short lists.
--   For larger collections, use Data.Set

module Agda.Utils.NubList where

import Control.Monad

import Data.Foldable
import Data.List
import Data.Monoid
-- import Data.Traversable

import Agda.Utils.Pointed

-- | Lists without duplicates.  Unchecked!
newtype NubList a = NubList { nubList :: [a] }
  deriving (Eq, Ord, Foldable)

-- not a proper Functor
-- , Functor, Traversable)

instance Show a => Show (NubList a) where
  show = show . nubList

instance Eq a => Monoid (NubList a) where
  mempty        = NubList []
  mappend xs ys = NubList $ nub (nubList xs ++ nubList ys)
  mconcat xss   = NubList $ nub (nubList =<< xss)

instance Pointed NubList where
  point a = NubList [a]

{- Not a proper monad, because Eq a is required

instance Monad NubList where
  return a = NubList $ return a
  m >>= k  = NubList $ nub (nubList . k =<< nubList m)
  fail err = NubList $ fail err

instance MonadPlus NubList where
  mzero = mempty
  mplus = mappend

-}

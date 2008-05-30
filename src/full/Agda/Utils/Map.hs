{-# OPTIONS -cpp #-}

module Agda.Utils.Map where

import Prelude hiding (map, lookup, mapM)
import Control.Applicative
import Data.Map
import Data.Traversable
import Agda.Utils.Monad

#include "../undefined.h"
import Agda.Utils.Impossible

data EitherOrBoth a b = L a | B a b | R b

-- | Not very efficient (goes via a list), but it'll do.
unionWithM :: (Ord k, Functor m, Monad m) => (a -> a -> m a) -> Map k a -> Map k a -> m (Map k a)
unionWithM f m1 m2 = fromList <$> mapM combine (toList m)
    where
	m = unionWith both (map L m1) (map R m2)

	both (L a) (R b) = B a b
	both _     _	 = __IMPOSSIBLE__

	combine (k, B a b) = (,) k <$> f a b
	combine (k, L a)   = return (k, a)
	combine (k, R b)   = return (k, b)

insertWithKeyM :: (Ord k, Monad m) => (k -> a -> a -> m a) -> k -> a -> Map k a -> m (Map k a)
insertWithKeyM clash k x m =
    case lookup k m of
	Just y	-> do
	    z <- clash k x y
	    return $ insert k z m
	Nothing	-> return $ insert k x m

-- | Filter a map based on the keys.
filterKeys :: Ord k => (k -> Bool) -> Map k a -> Map k a
filterKeys p = filterWithKey (const . p)


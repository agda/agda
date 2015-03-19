{- We need to keep the dependency on containers below 5.0 in
   order to avoid giving rise to unsolvable constraints on
   older versions of GHC (7.4.2 at the moment) -}

{-# LANGUAGE CPP #-}

module Agda.Utils.Map.Compat where

import Control.Applicative
import Data.Traversable
import qualified Data.Map as Map
import Data.Map (Map, fromList, toList)

traverseWithKey :: (Ord k, Applicative t) => (k -> a -> t b) -> Map k a -> t (Map k b)
#if !MIN_VERSION_containers(5,0,0)
traverseWithKey f m = fromList <$> traverse (\ (k, v) -> (,) k <$> f k v) (toList m)
#else
traverseWithKey = Map.traverseWithKey
#endif


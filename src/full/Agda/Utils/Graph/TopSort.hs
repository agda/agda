{-# language ViewPatterns #-}
module Agda.Utils.Graph.TopSort
    ( topSort
    ) where

import Data.List
import Data.Maybe
import Data.Function
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Arrow

mergeBy :: (a -> a -> Bool) -> [a] -> [a] -> [a]
mergeBy _ [] xs = xs
mergeBy _ xs [] = xs
mergeBy f (x:xs) (y:ys)
    | f x y = x: mergeBy f xs (y:ys)
    | otherwise = y: mergeBy f (x:xs) ys

-- | topoligical sort with smallest-numbered available vertex first
-- | input: nodes, edges
-- | output is Nothing if the graph is not a DAG
topSort :: Ord n => [n] -> [(n, n)] -> Maybe [n]
topSort nodes edges = mergeBy (<) nodes' <$> g m is
  where
    g m []
        | Map.null m = Just []
        | otherwise = Nothing
    g m ((n, Set.toList -> cs): ns)
        = (n:) <$> g m' (mergeBy ((<) `on` fst) ns [(c, s) | c<-cs, (0, s) <- maybeToList $ Map.lookup c m'])
      where
        m' = foldr (Map.adjust $ first (+(-1))) (Map.delete n m) cs

    is = map (second snd) . filter ((==0) . fst . snd) $ Map.toList m

    nodes' = Set.toList $ Set.fromList nodes `Set.difference` Set.fromList (concatMap (\(a,b)->[a,b]) edges)

    m = foldr f mempty $ nub edges
    f (b, a)
        = Map.alter (Just . maybe (1, mempty) (first (+1))) b
        . Map.alter (Just . maybe (0, Set.singleton b) (second $ Set.insert b)) a

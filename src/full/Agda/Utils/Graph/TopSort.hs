
module Agda.Utils.Graph.TopSort
    ( topSort
    ) where

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as G

-- NB:: Defined but not used
mergeBy :: (a -> a -> Bool) -> [a] -> [a] -> [a]
mergeBy _ [] xs = xs
mergeBy _ xs [] = xs
mergeBy f (x:xs) (y:ys)
    | f x y = x: mergeBy f xs (y:ys)
    | otherwise = y: mergeBy f (x:xs) ys

-- | topoligical sort with smallest-numbered available vertex first
-- | input: nodes, edges
-- | output is Nothing if the graph is not a DAG
--   Note: should be stable to preserve order of generalizable variables. Algorithm due to Richard
--   Eisenberg, and works by walking over the list left-to-right and moving each node the minimum
--   distance left to guarantee topological ordering.
topSort :: Ord n => Set n -> [(n, n)] -> Maybe [n]
topSort nodes edges = go [] (Set.toList nodes)
  where
    -- #4253: The input edges do not necessarily include transitive dependencies, so take transitive
    --        closure before sorting.
    w      = Just () -- () is not a good edge label since it counts as a "zero" edge and will be ignored
    g      = G.transitiveClosure $
               G.fromNodeSet nodes `G.union`
               G.fromEdges [G.Edge a b w | (a, b) <- edges]
    -- Only the keys of these maps are used.
    deps a = G.graph g Map.! a

    -- acc: Already sorted nodes in reverse order paired with accumulated set of nodes that must
    -- come before it
    go acc [] = Just $ reverse $ map fst acc
    go acc (n : ns) = (`go` ns) =<< insert n acc

    insert a [] = Just [(a, deps a)]
    insert a bs0@((b, before_b) : bs)
      | before && after = Nothing
      | before          = ((b, Map.union before_a before_b) :) <$> insert a bs  -- a must come before b
      | otherwise       = Just $ (a, Map.union before_a before_b) : bs0
      where
        before_a = deps a
        before = Map.member a before_b
        after  = Map.member b before_a

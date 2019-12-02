{-# language ViewPatterns #-}
module Agda.Utils.Graph.TopSort
    ( topSort
    ) where

import Data.List
import Data.Maybe
import Data.Function
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Graph as Graph
import Control.Arrow
import Agda.Utils.List (nubOn)

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
topSort :: Ord n => [n] -> [(n, n)] -> Maybe [n]
topSort nodes edges = go [] nodes
  where
    deps = (Map.!) $ Map.fromList [ (a, Set.fromList [ b | (a1, b) <- edges, a == a1 ]) | a <- nodes ]

    -- acc: Already sorted nodes in reverse order paired with accumulated set of nodes that must
    -- come before it
    go acc [] = Just $ reverse $ map fst acc
    go acc (n : ns) = (`go` ns) =<< insert n acc

    insert a [] = Just [(a, deps a)]
    insert a bs0@((b, before_b) : bs)
      | before && after = Nothing
      | before          = ((b, Set.union before_a before_b) :) <$> insert a bs  -- a must come before b
      | otherwise       = Just $ (a, Set.union before_a before_b) : bs0
      where
        before_a = deps a
        before = Set.member a before_b
        after  = Set.member b before_a


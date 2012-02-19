{-# LANGUAGE DeriveFunctor #-}
module Agda.Utils.Graph where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Map (Map)
import Data.Set (Set)

import Agda.Utils.SemiRing

-- Only one edge between any two nodes.
newtype Graph n e = Graph { unGraph :: Map n (Map n e) }
  deriving (Eq, Functor)

edges :: Ord n => Graph n e -> [(n, n, e)]
edges g = concatMap onNode $ Map.assocs $ unGraph g
  where
    onNode (from, es) = map (onNeighbour from) $ Map.assocs es
    onNeighbour from (to, w) = (from, to, w)

nodes :: Ord n => Graph n e -> Set n
nodes = Set.fromList . concatMap f . edges
  where f (a, b, _) = [a, b]

fromList :: (SemiRing e, Ord n) => [(n, n, e)] -> Graph n e
fromList es = unions [ singleton a b w | (a, b, w) <- es ]

empty :: Graph n e
empty = Graph Map.empty

singleton :: n -> n -> e -> Graph n e
singleton a b w = Graph $ Map.singleton a (Map.singleton b w)

insert :: (SemiRing e, Ord n) => n -> n -> e -> Graph n e -> Graph n e
insert from to w g = union (singleton from to w) g

union :: (SemiRing e, Ord n) => Graph n e -> Graph n e -> Graph n e
union (Graph g1) (Graph g2) =
  Graph $ Map.unionWith (Map.unionWith oplus) g1 g2

unions :: (SemiRing e, Ord n) => [Graph n e] -> Graph n e
unions = foldr union empty

lookup :: Ord n => n -> n -> Graph n e -> Maybe e
lookup a b g = Map.lookup b =<< Map.lookup a (unGraph g)

neighbours :: Ord n => n -> Graph n e -> [(n, e)]
neighbours a g = maybe [] Map.assocs $ Map.lookup a $ unGraph g

growGraph :: (SemiRing e, Ord n) => Graph n e -> Graph n e
growGraph g = foldr union g $ map newEdges $ edges g
  where
    newEdges (a, b, w) = case Map.lookup b (unGraph g) of
        Just es -> Graph $ Map.singleton a $ Map.map (otimes w) es
        Nothing -> empty

-- | Computes the transitive closure of the graph.
--
-- Note that this algorithm is not guaranteed to terminate for
-- arbitrary semirings.

transitiveClosure :: (Eq e, SemiRing e, Ord n) => Graph n e -> Graph n e
transitiveClosure g = loop g
  where -- n = Set.size $ nodes g
    loop g | g == g'   = g
           | otherwise = loop g'
      where
        g' = growGraph g


findPath :: (SemiRing e, Ord n) => (e -> Bool) -> n -> n -> Graph n e -> Maybe e
findPath good a b g = case filter good $ allPaths good a b g of
  []    -> Nothing
  w : _ -> Just w

allPaths :: (SemiRing e, Ord n, Ord c) => (e -> c) -> n -> n -> Graph n e -> [e]
allPaths classify a b g = paths Set.empty a
  where
    paths visited a = concatMap step $ neighbours a g
      where
        step (c, w)
          | Set.member tag visited = []
          | otherwise = found ++
                        map (otimes w)
                          (paths (Set.insert tag visited) c)
          where tag = (c, classify w)
                found | b == c    = [w]
                      | otherwise = []

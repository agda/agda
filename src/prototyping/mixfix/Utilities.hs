------------------------------------------------------------------------
-- Miscellaneous helper functions
------------------------------------------------------------------------

module Utilities
  ( -- * Graph utilities
    acyclic
  , graph
  , acyclicGraph
  , shrinkGraph
    -- * Map/set utilities
  , map'
  , (!)
    -- * List utilities
  , sublist
  , distinct
  , efficientNub
  , tests
  ) where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.List as List
import Data.Graph.Inductive
import Control.Monad
import Data.Function
import Test.QuickCheck

------------------------------------------------------------------------
-- Graph utilities

-- | Is the graph acyclic?

-- Check this by ensuring that the graph is simple (no loops) and all
-- strongly connected components have size 1.

acyclic :: Graph gr => gr n e -> Bool
acyclic g = isSimple g && all (\c -> length c == 1) (scc g)

-- | Is the graph a graph (as opposed to a multi-graph), i.e. is there
-- at most one directed edge from any node to another?

graph :: Graph gr => gr n e -> Bool
graph g = all (distinct . suc g) (nodes g)

-- | Generates an acyclic graph (not a multi-graph).

acyclicGraph :: Graph gr => Gen node -> Gen edge -> Gen (gr node edge)
acyclicGraph nodeG edgeG = do
  NonNegative n <- fmap smaller arbitrary
  let nodes = [1 .. n]
  lNodes <- mapM (\n -> liftM ((,) n) nodeG) nodes
  lEdges <- liftM concat $ mapM edges nodes
  return $ mkGraph lNodes lEdges
  where
  smaller n | n <= 3    = n
            | otherwise = n `div` 3

  -- Generates edges from prior nodes to n.
  edges n | n <= 1 = return []
  edges n = do
    NonNegative len <- fmap smaller arbitrary
    liftM (List.nubBy ((==) `on` fst3)) $
      vectorOf len (liftM3 (,,) (choose (1, n - 1)) (return n) edgeG)

  fst3 (x, y, z) = x

prop_acyclicGraph =
  forAll (acyclicGraph arbitrary arbitrary
            :: Gen (Gr Integer Bool)) $ \g ->
    acyclic g && graph g

-- | Shrinks a graph by removing a node or an edge, or shrinking a
-- node or an edge.

shrinkGraph :: (DynGraph gr, Arbitrary node, Arbitrary edge, Eq edge) =>
               gr node edge -> [gr node edge]
shrinkGraph g = map (flip delNode g) (nodes g) ++
                map (flip delEdge g) (edges g) ++
                concatMap shrinkNode (nodes g) ++
                concatMap shrinkEdge (edges' g)
  where
  shrinkNode n = case match n g of
    (Nothing, _)                -> []
    (Just (to, n, x, from), g') ->
       map (\x' -> (to, n, x', from) & g') (shrink x)

  edges' :: DynGraph gr => gr node edge -> [LEdge edge]
  edges' g = concatMap (\from -> map (\(to, x) -> (from, to, x))
                                     (lsuc g from))
                       (nodes g)

  shrinkEdge e@(n1, n2, x) =
    map (\x' -> insEdge (n1, n2, x') (delLEdge e g)) (shrink x)

------------------------------------------------------------------------
-- Map/set utilities

-- | Converts a set to a list and maps over it.

map' :: (a -> b) -> Set a -> [b]
map' f = map f . Set.toList

-- | A (safe) variant of 'Map.(!)'.

(!) :: Ord k => Map k (Set v) -> k -> Set v
m ! k = case Map.lookup k m of
  Nothing -> Set.empty
  Just ns -> ns

------------------------------------------------------------------------
-- List utilities

-- | Generates a sublist of the given list.

sublist :: [a] -> Gen [a]
sublist xs = fmap concat $ mapM possibly xs
  where possibly x = oneof [return [], return [x]]

prop_sublist (NonNegative n) =
  forAll (sublist [1 .. n]) $ \xs ->
    distinct xs && xs == List.sort xs

-- | Are all elements in the list distinct?

distinct :: Ord a => [a] -> Bool
distinct xs = List.sort xs == efficientNub xs

prop_distinct1 (NonEmpty xs)   = not (distinct $ xs ++ xs)
prop_distinct2 (NonNegative n) = distinct [1 .. n]

-- | An efficient variant of 'List.nub'. Note that the resulting list
-- is sorted.

efficientNub :: Ord a => [a] -> [a]
efficientNub = removeDups . List.sort
  where removeDups = map head . List.group

------------------------------------------------------------------------
-- Code used to test efficientNub

data IgnoreSnd a b = Pair a b
  deriving Show

fst' :: IgnoreSnd a b -> a
fst' (Pair x y) = x

instance (Eq a, Eq b) => Eq (IgnoreSnd a b) where
  (==) = (==) `on` fst'

instance (Ord a, Eq b) => Ord (IgnoreSnd a b) where
  compare = compare `on` fst'

instance (Arbitrary a, Arbitrary b) => Arbitrary (IgnoreSnd a b) where
  arbitrary = liftM2 Pair arbitrary arbitrary

-- | This property tests that 'efficientNub' is equivalent to 'nub',
-- up to a permutation of the output. Note that the property checks
-- that the two functions choose the same representative from every
-- equivalence class.

prop_efficientNub :: [IgnoreSnd Integer Int] -> Property
prop_efficientNub xs =
  classify nonTriv "with non-trivial equivalence classes" $
    efficientNub xs =*= List.sort (List.nub xs)
  where
  xs =*= ys = length xs == length ys && and (zipWith reallyEqual xs ys)
  reallyEqual (Pair x y) (Pair u v) = x == u && y == v

  nonTriv = any ((> 1) . length) $
            map (List.nubBy reallyEqual) $
            List.group $ List.sort xs

------------------------------------------------------------------------
-- All test cases

-- | All tests from this module.

tests = do
  quickCheck prop_acyclicGraph
  quickCheck (prop_sublist   :: NonNegative Integer -> Property)
  quickCheck (prop_distinct1 :: NonEmptyList [Integer] -> Bool)
  quickCheck (prop_distinct2 :: NonNegative Integer -> Bool)
  quickCheck prop_efficientNub

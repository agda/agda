------------------------------------------------------------------------
-- Miscellaneous helper functions
------------------------------------------------------------------------

module Utilities
  ( -- * Graph utilities
    acyclic
  , graph
  , simpleGraph
  , acyclicGraph
  , shrinkGraph
    -- * Map/set utilities
  , (!)
  , setToMap
    -- * List utilities
  , sublist
  , partitionsOf
  , list
  , pairUp
  , distinct
  , separate
  , twoAdjacent
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
import Text.Show.Functions

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

-- | Generates a simple graph. The first argument is a list containing
-- all the node annotations (so the length of the list determines the
-- number of nodes in the graph).

simpleGraph :: Graph gr => [node] -> Gen edge -> Gen (gr node edge)
simpleGraph nodes edge =
  liftM (mkGraph ns . concat) $ mapM edges (map fst ns)
  where
  size = length nodes
  ns   = zip [1..] nodes

  -- Generates edges from arbitrary nodes to n.
  edges n | size <= 1 = return []
  edges n = do
    len <- choose (0, size - 1)
    liftM (List.nubBy ((==) `on` fst3)) $
      vectorOf len (liftM3 (,,) target (return n) edge)
    where
    target = do
      t <- choose (1, size - 1)
      return $ if t == n then size else t

  fst3 (x, y, z) = x

prop_simpleGraph ns =
  forAll (simpleGraph ns arbitrary :: Gen (Gr Integer Bool)) $ \g ->
    isSimple g && graph g

-- | Generates an acyclic graph (not a multi-graph). The first
-- argument is a list containing all the node annotations (so the
-- length of the list determines the number of nodes in the graph).

acyclicGraph :: Graph gr =>
                [node] -> Gen edge -> Gen (gr node edge)
acyclicGraph nodes edge =
  liftM (mkGraph ns . concat) $ mapM edges (map fst ns)
  where
  ns = zip [1..] nodes

  -- Generates edges from prior nodes to n.
  edges n | n <= 1 = return []
  edges n = do
    len <- choose (0, n - 1)
    liftM (List.nubBy ((==) `on` fst3)) $
      vectorOf len (liftM3 (,,) (choose (1, n - 1)) (return n) edge)

  fst3 (x, y, z) = x

prop_acyclicGraph ns =
  forAll (acyclicGraph ns arbitrary :: Gen (Gr Integer Bool)) $ \g ->
    acyclic g && graph g

-- | Shrinks a graph by removing a node or an edge.

shrinkGraph :: DynGraph gr => gr node edge -> [gr node edge]
shrinkGraph g = map (flip delNode g) (nodes g) ++
                map (flip delEdge g) (edges g)

-- | Shrinks a graph by removing a node or an edge, or shrinking a
-- node or an edge.

shrinkGraph' :: (DynGraph gr, Arbitrary node, Arbitrary edge, Eq edge) =>
                gr node edge -> [gr node edge]
shrinkGraph' g = shrinkGraph g ++
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

-- | A (safe) variant of 'Map.(!)'.

(!) :: Ord k => Map k (Set v) -> k -> Set v
m ! k = case Map.lookup k m of
  Nothing -> Set.empty
  Just ns -> ns

-- | Converts a set to a finite map.

setToMap :: Set k -> Map k ()
setToMap =
  Map.fromDistinctAscList . map (\x -> (x, ())) . Set.toAscList

------------------------------------------------------------------------
-- List utilities

-- | Generates a sublist of the given list.

sublist :: [a] -> Gen [a]
sublist xs = fmap concat $ mapM possibly xs
  where possibly x = oneof [return [], return [x]]

prop_sublist (NonNegative n) =
  forAll (sublist [1 .. n]) $ \xs ->
    distinct xs && xs == List.sort xs

-- | @partitionsOf xs@ generates a number of non-empty lists that
-- partition @xs@.
--
-- Precondition: @xs@ has to be finite.

partitionsOf :: [a] -> Gen [[a]]
partitionsOf xs = fmap split $ pairUp xs (choose (1, length xs))
  where
  split =
    map (map fst) .
    List.groupBy ((==) `on` snd) .
    List.sortBy (compare `on` snd)

prop_partitionsOf xs =
  forAll (partitionsOf xs) $ \xxs ->
    concat xxs =^= xs &&
    all (not . null) xxs
  where (=^=) = (==) `on` List.sort

-- | @list l g@ generates a list whoose length is determined by @l@,
-- containing elements determined by @g@.

list :: Integral i => Gen i -> Gen a -> Gen [a]
list l g = do
  len <- l
  sequence $ List.genericReplicate len g

prop_list (NonNegative m') (NonNegative n') =
  forAll (list (choose (m, m + n)) arbitrary :: Gen [()]) $ \xs ->
    m <= length xs && length xs <= m + n
  where
  [m, n] = map (`min` 100) [m', n']

-- | @pairUp xs g@ pairs up every element from @xs@ with an element
-- generated by @g@.

pairUp :: [a] -> Gen b -> Gen [(a, b)]
pairUp xs g = fmap (zip xs) $ sequence $ repeat g

prop_pairUp xs =
  forAll (pairUp xs arbitrary :: Gen [(Integer, Bool)]) $ \xys ->
    map fst xys == xs

-- | Are all elements in the list distinct?

distinct :: Ord a => [a] -> Bool
distinct xs = List.sort xs == efficientNub xs

prop_distinct1 (NonEmpty xs)   = not (distinct $ xs ++ xs)
prop_distinct2 (NonNegative n) = distinct [1 .. n]

-- | Splits up a list, using the predicate to identify separators. The
-- separators are retained in the output, in singleton lists.

separate :: (a -> Bool) -> [a] -> [[a]]
separate p = List.groupBy ((&&) `on` not . p)

prop_separate p xs =
  classify (length segments == 1) "trivial" $
    all (not . null) segments &&
    all (\s -> if length s > 1 then all (not . p) s else True) segments
  where segments = separate p xs

-- Does the list contain two adjacent elements satisfying the
-- predicate?

twoAdjacent :: (a -> Bool) -> [a] -> Bool
twoAdjacent p ys = case ys of
  [] -> False
  ps -> anyPair ((&&) `on` p) $ zip (init ps) (tail ps)
    where anyPair p = any (uncurry p)

prop_twoAdjacent p xs x ys =
  (twoAdjacent p list || twoAdjacent (not . p) list) &&
  not (twoAdjacent (const False) xs) &&
  not (twoAdjacent p [x]) &&
  not (twoAdjacent p [])
  where list = xs ++ [x, x] ++ ys

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
  quickCheck prop_simpleGraph
  quickCheck prop_acyclicGraph
  quickCheck (prop_sublist      :: NonNegative Integer -> Property)
  quickCheck (prop_partitionsOf :: [Integer] -> Property)
  quickCheck prop_list
  quickCheck prop_pairUp
  quickCheck (prop_distinct1    :: NonEmptyList [Integer] -> Bool)
  quickCheck (prop_distinct2    :: NonNegative Integer -> Bool)
  quickCheck (prop_separate     :: (Integer -> Bool) -> [Integer] ->
                                   Property)
  quickCheck (prop_twoAdjacent  :: (Integer -> Bool) ->
                                   [Integer] -> Integer -> [Integer] ->
                                   Bool)
  quickCheck prop_efficientNub

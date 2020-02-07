{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.Warshall ( tests ) where

--import Agda.Syntax.Common ( Nat )
import Agda.Utils.Warshall

import Data.List
import qualified Data.Map as Map
import Data.Maybe

import Internal.Helpers

type Nat = Int
-- Testing ----------------------------------------------------------------

genGraph :: Ord node => Float -> Gen edge -> [node] -> Gen (AdjList node edge)
genGraph density edge nodes = do
  Map.fromList . concat <$> mapM neighbours nodes
  where
    k = round (100 * density)
    neighbours n = do
      ns <- concat <$> mapM neighbour nodes
      case ns of
        []  -> elements [[(n, [])], []]
        _   -> return [(n, ns)]
    neighbour n = frequency
      [ (k, do e <- edge
               ns <- neighbour n
               return ((n, e):ns))
      , (100 - k, return [])
      ]

type Distance = Weight

genGraph_ :: Nat -> Gen (AdjList Nat Distance)
genGraph_ n =
  genGraph 0.2 (Finite <$> natural) [0..n - 1]

lookupEdge :: Ord n => n -> n -> AdjList n e -> Maybe e
lookupEdge i j g = lookup j =<< Map.lookup i g

edges :: AdjList n e -> [(n,n,e)]
edges g = do
  (i, ns) <- Map.toList g
  (j, e)  <- ns
  return (i, j, e)

-- | Check that no edges get longer when completing a graph.
no_tested_prop_smaller :: Nat -> Property
no_tested_prop_smaller n' =
  forAll (genGraph_ n) $ \g ->
  let g' = warshallG g in
  and [ lookupEdge i j g' =< e
      | (i, j, e) <- edges g
      ]
  where
    n = abs (div n' 2)
    Nothing =< _ = False
    Just x  =< y = x <= y

newEdge :: Nat -> Nat -> Distance -> AdjList Nat Distance ->
           AdjList Nat Distance
newEdge i j e = Map.insertWith (++) i [(j, e)]

genPath :: Nat -> Nat -> Nat -> AdjList Nat Distance ->
           Gen (AdjList Nat Distance)
genPath n i j g = do
  es <- listOf $ (,) <$> node <*> edge
  v  <- edge
  return $ addPath i (es ++ [(j, v)]) g
  where
    edge :: Gen Distance
    edge = Finite <$> natural

    node :: Gen Nat
    node = choose (0, n - 1)

    addPath :: Nat -> [(Nat, Distance)] -> AdjList Nat Distance ->
               AdjList Nat Distance
    addPath _ []          g = g
    addPath i ((j, v):es) g = newEdge i j v $ addPath j es g

-- | Check that all transitive edges are added.
no_tested_prop_path :: Nat -> Property
no_tested_prop_path n' =
  forAll (genGraph_ n) $ \g ->
  forAll (two $ choose (0, n - 1)) $ \(i, j) ->
  forAll (genPath n i j g) $ \g' ->
  isJust (lookupEdge i j $ warshallG g')
  where
    n = abs (div n' 2) + 1

mapNodes :: Ord node' => (node -> node') -> AdjList node edge -> AdjList node' edge
mapNodes f = Map.map f' . Map.mapKeys f
  where
    f' es = [ (f n, e) | (n,e) <- es ]

-- | Check that no edges are added between components.
no_tested_prop_disjoint :: Nat -> Property
no_tested_prop_disjoint n' =
  forAll (two $ genGraph_ n) $ \(g1, g2) ->
  let g  = Map.union (mapNodes Left g1) (mapNodes Right g2)
      g' = warshallG g
  in all disjoint (Map.assocs g')
  where
    n = abs (div n' 3)
    disjoint (Left i, es)  = all (isLeft . fst) es
    disjoint (Right i, es) = all (isRight . fst) es
    isLeft = either (const True) (const False)
    isRight = not . isLeft

no_tested_prop_stable :: Nat -> Property
no_tested_prop_stable n' =
  forAll (genGraph_ n) $ \g ->
  let g' = warshallG g in
  g' =~= warshallG g'
  where
    n = abs (div n' 2)
    g =~= g' = sort (edges g) == sort (edges g')

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $allProperties work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'allProperties'.
--
-- Using 'allProperties' is convenient and superior to the manual
-- enumeration of tests, since the name of the property is added
-- automatically.

tests :: TestTree
tests = testProperties "Internal.Utils.Warshall" $allProperties


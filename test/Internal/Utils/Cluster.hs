{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.Cluster ( tests ) where

import Agda.Utils.Cluster

import Data.Char
import Data.List (delete, intersect, sort)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Foldable as Fold

import Internal.Helpers

------------------------------------------------------------------------
-- * Properties
------------------------------------------------------------------------

-- | A type used for the tests.

type C = Int

-- Fundamental properties: soundness and completeness

-- | Not too many clusters.  (Algorithm equated all it could.)
--
--   Each element in a cluster shares a characteristic with at least one
--   other element in the same cluster.
prop_cluster_complete :: Fun Int (NonEmpty C) -> [Int] -> Bool
prop_cluster_complete (Fun _ f) as =
  (`all` cluster f as) $ \ cl ->
  (`all` cl) $ \ a ->
  let csa = NonEmpty.toList $ f a in
  let cl' = delete a $ NonEmpty.toList cl in
  -- Either a is the single element of the cluster, or it shares a characteristic c
  -- with some other element b of the same cluster.
  null cl' || not (null [ (b,c) | b <- cl', c <- NonEmpty.toList (f b), c `elem` csa ])

-- | Not too few clusters.  (Algorithm did not equate too much.)
--
--   Elements of different clusters share no characteristics.
prop_cluster_sound :: Fun Int (NonEmpty C) -> [Int] -> Bool
prop_cluster_sound (Fun _ f) as =
  (`all` [ (c, d) | let cs = cluster f as, c <- cs, d <- cs, c /= d]) $ \ (c, d) ->
  (`all` c) $ \ a ->
  (`all` d) $ \ b ->
  null $ (NonEmpty.toList $ f a) `intersect` (NonEmpty.toList $ f b)

isSingleton, exactlyTwo, atLeastTwo :: Foldable t => t a -> Bool
isSingleton x = Fold.length x == 1
exactlyTwo  x = Fold.length x == 2
atLeastTwo  x = Fold.length x >= 2

prop_cluster_empty :: Bool
prop_cluster_empty =
  null (cluster (const (0 :| [])) [])

prop_cluster_permutation :: Fun Int (NonEmpty C) -> [Int] -> Bool
prop_cluster_permutation (Fun _ f) as =
  sort as == sort (concatMap NonEmpty.toList (cluster f as))

prop_cluster_single :: a -> [a] -> Bool
prop_cluster_single a as =
  isSingleton $ cluster (const (0 :| [])) $ (a:as)

prop_cluster_idem :: Fun a (NonEmpty C) -> NonEmpty a -> Bool
prop_cluster_idem (Fun _ f) as =
  isSingleton $ cluster1 f $ NonEmpty.head $ cluster1 f as

prop_two_clusters :: [Int] -> Bool
prop_two_clusters as =
  atLeastTwo $ cluster (\ x -> x :| [x]) (-1:1:as)

-- | An example.
--
--   "anabel" is related to "babel" (common letter 'a' in 2-letter prefix)
--   which is related to "bond" (common letter 'b').
--
--   "hurz", "furz", and "kurz" are all related (common letter 'u').
test :: [NonEmpty String]
test = cluster (\ (x:y:_) -> ord x :| [ord y])
         ["anabel","bond","babel","hurz","furz","kurz"]

prop_test :: Bool
prop_test = test ==
  [ "anabel" :| "bond" : "babel" : []
  , "hurz"   :| "furz" : "kurz"  : []
  ]

-- | Modified example (considering only the first letter).
test1 :: [NonEmpty String]
test1 = cluster (\ (x:_:_) -> ord x :| [])
          ["anabel","bond","babel","hurz","furz","kurz"]

prop_test1 :: Bool
prop_test1 = test1 ==
  [ "anabel" :| []
  , "bond"   :| "babel" : []
  , "furz"   :| []
  , "hurz"   :| []
  , "kurz"   :| []
  ]

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
tests = testProperties "Internal.Utils.Cluster" $allProperties

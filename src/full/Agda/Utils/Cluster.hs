{-# OPTIONS_GHC -Wunused-imports #-}

-- | Create clusters of non-overlapping things.

module Agda.Utils.Cluster
  ( cluster
  , cluster'
  , cluster1
  , cluster1'
  ) where

import Control.Monad

-- An imperative union-find library:
import Data.Equivalence.Monad ( runEquivT, equateAll, classDesc )

-- NB: We keep this module independent of Agda.Utils.List1
import Data.List.NonEmpty     ( NonEmpty(..), nonEmpty, toList )
import Data.Maybe             ( fromMaybe )

import qualified Data.Map.Strict as MapS

import Agda.Utils.Functor
import Agda.Utils.Singleton
import Agda.Utils.Fail

-- | Given a function @f :: a -> NonEmpty c@ which returns a non-empty list of
--   characteristics of @a@, partition a list of @a@s into groups such
--   that each element in a group shares at least one characteristic
--   with at least one other element of the group.
cluster :: Ord c => (a -> NonEmpty c) -> [a] -> [NonEmpty a]
cluster = liftList1 . cluster1

-- | Partition a list of @a@s paired with a non-empty list of
--   characteristics into groups such that each element in a group
--   shares at least one characteristic with at least one other
--   element of the group.
cluster' :: Ord c => [(a, NonEmpty c)] -> [NonEmpty a]
cluster' = liftList1 cluster1'

-- | Lift a function on non-empty lists to a function on lists.
--
-- Duplicate of 'Agda.Utils.List1.liftList1'.
liftList1 :: (NonEmpty a -> NonEmpty b) -> [a] -> [b]
liftList1 f = \case
  []     -> []
  a : as -> toList $ f $ a :| as

-- | Given a function @f :: a -> NonEmpty c@ which returns a non-empty list of
--   characteristics of @a@, partition a non-empty list of @a@s into groups such
--   that each element in a group shares at least one characteristic
--   with at least one other element of the group.
cluster1 :: Ord c => (a -> NonEmpty c) -> NonEmpty a -> NonEmpty (NonEmpty a)
cluster1 f as = cluster1' $ fmap (\ a -> (a, f a)) as

-- | Partition a non-empty list of @a@s paired with a non-empty list of
--   characteristics into groups such that each element in a group
--   shares at least one characteristic with at least one other
--   element of the group.
cluster1' :: Ord c => NonEmpty (a, NonEmpty c) -> NonEmpty (NonEmpty a)
cluster1' acs = runFail_ $ runEquivT id const $ do
  -- Construct the equivalence classes of characteristics.
  forM_ acs $ \ (_, c :| cs) -> equateAll $ c:cs
  -- Pair each element with its class.
  cas <- forM acs $ \ (a, c :| _) -> classDesc c <&> \ k -> MapS.singleton k (singleton a)
  -- Create a map from class to elements.
  let m = MapS.unionsWith (<>) cas
  -- Return the values of the map
  return $ fromMaybe (error "impossibility at Agda.Utils.Cluster.cluster'") $ nonEmpty $
    MapS.elems m

{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wunused-imports #-}

-- | Var field implementation of sets of (small) natural numbers.

module Agda.Utils.VarSet
  ( VarSet
  , empty, insert, singleton, union, unions
  , fromList, toList, toAscList, toDescList
  , disjoint, isSubsetOf, member, IntSet.null
  , delete, difference, IntSet.filter, intersection
  , mapMonotonic, Agda.Utils.VarSet.subtract
  )
  where

import Data.IntSet as IntSet

type VarSet = IntSet

#if !MIN_VERSION_containers(0,6,3)
mapMonotonic :: (Int -> Int) -> VarSet -> VarSet
mapMonotonic f = fromDistinctAscList . fmap f . toAscList
#endif

subtract :: Int -> VarSet -> VarSet
subtract n = mapMonotonic (Prelude.subtract n)

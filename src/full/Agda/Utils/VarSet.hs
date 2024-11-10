{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wunused-imports #-}

-- | Manage sets of natural numbers (de Bruijn indices).

module Agda.Utils.VarSet
  ( VarSet
  , empty, insert, singleton, union, unions
  , fromList, toList, toAscList, toDescList
  , disjoint, isSubsetOf, member, IntSet.null
  , delete, difference, IntSet.filter, filterGE, intersection
  , mapMonotonic, Agda.Utils.VarSet.subtract
  )
  where

import Data.IntSet as IntSet

type VarSet = IntSet

#if !MIN_VERSION_containers(0,6,3)
mapMonotonic :: (Int -> Int) -> VarSet -> VarSet
mapMonotonic f = fromDistinctAscList . fmap f . toAscList
#endif

-- | Subtract from each element.
subtract :: Int -> VarSet -> VarSet
subtract n = mapMonotonic (Prelude.subtract n)

-- | Keep only elements greater or equal to the given pivot.
filterGE :: Int -> VarSet -> VarSet
filterGE n = snd . IntSet.split (n - 1)

{-# LANGUAGE CPP #-}

-- | Var field implementation of sets of (small) natural numbers.

module Agda.Utils.VarSet
  ( VarSet
  , union, unions, member, empty, delete, singleton
  , fromList, toList, toDescList
  , isSubsetOf, IntSet.null
  , intersection, difference
  , Agda.Utils.VarSet.subtract
  )
  where

import Data.IntSet as IntSet

-- TODO Víctor (2021-03-04)
-- This should be implemented using `Agda.Utils.IntSet.Typed`
type VarSet = IntSet

subtract :: Int -> VarSet -> VarSet
#if MIN_VERSION_containers(0,6,3)
subtract n = IntSet.mapMonotonic (Prelude.subtract n)
#else
subtract n = IntSet.map (Prelude.subtract n)
#endif

{-
import Data.Bits

type VarSet = Integer
type Var    = Integer

union :: VarSet -> VarSet -> VarSet
union = (.|.)

member :: Var -> VarSet -> Bool
member b s = testVar s (fromIntegral b)

empty :: VarSet
empty = 0

delete :: Var -> VarSet -> VarSet
delete b s = clearVar s (fromIntegral b)

singleton :: Var -> VarSet
singleton = bit

subtract :: Int -> VarSet -> VarSet
subtract n s = shiftR s n

fromList :: [Var] -> VarSet
fromList = foldr (union . singleton . fromIntegral) empty

isSubsetOf :: VarSet -> VarSet -> Bool
isSubsetOf s1 s2 = 0 == (s1 .&. complement s2)

toList :: VarSet -> [Var]
toList s = loop 0 s
  where
    loop i 0 = []
    loop i n
      | testVar n 0 = fromIntegral i : (loop $! i + 1) (shiftR n 1)
      | otherwise   = (loop $! i + 1) (shiftR n 1)
-}

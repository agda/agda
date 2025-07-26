-- Needed to get haddock to pick up on identifiers with a #.
{-# LANGUAGE MagicHash #-}

{-|
Manage sets of natural numbers (de Bruijn indices).

This file contains an implementation of finite sets of integers
that is optimized for storing sets of free variables. Notably,
de Bruijn indices/levels are not uniformly distributed across the
range of 'Int', and are always very small (EG: less than 64).

This makes 'Data.IntSet.IntSet' somewhat ill-suited for the task.
'Data.IntSet.IntSet' is designed to be able to handle values distributed
across the entire range of 'Int', at the cost of pointer indirections
and poor memory locality.

Instead, t'VarSet' stores free variables as a bitvector. When the
elements in the set are all smaller than 64, we can fit the entire set
into a single unboxed 'GHC.Base.Word#', which makes most of our set operations
a single instruction.

When we exceed this bound, we fall back to an unboxed 'GHC.Base.ByteArray#'.
Experimentally, this happens less than 0.0001% of the time.

= Experimental Results

Agda builds instrumented with 'traceVarSetSize' give the following
statistics for 'VarSet' sizes across the following libraries:

+-------------+------------------------------------------+-------------------+---------------------+
| library     | commit hash                              | varsets allocated | non-word sized sets |
+=============+==========================================+===================+=====================+
| 1lab        | 11f4672ca7dcfdccb1b4ce94ca4ca42c9b732e62 | 118198551         | 0                   |
+-------------+------------------------------------------+-------------------+---------------------+
| agda-stdlib | 0e97e2ed1f999ea0d2cce2a3b2395d5a9a7bd36a | 38960049          | 2178                |
+-------------+------------------------------------------+-------------------+---------------------+
| cubical     | 1f2af52701945bef003a525f78fa41aeadb7c6ae | 82751805          | 0                   |
+-------------+------------------------------------------+-------------------+---------------------+
-}

module Agda.Utils.VarSet
  ( VarSet(..)
  -- * Construction
  , empty
  , singleton
  , fromList
  , full
  -- * Insertion
  , insert
  -- * Deletion
  , delete
  -- * Queries
  , null
  , member
  , lookupMin
  , size
  , disjoint
  , isSubsetOf
  -- * Combining variable sets
  , union
  , unions
  , intersection
  , difference
  , (\\)
  , complement
  -- * Filters
  , split
  -- * Folds
  , foldr
  -- * Views
  , minView
  -- * Contextual operations
  , strengthen
  , weaken
  -- * Conversions
  , toDescList
  , toAscList
  )
  where


import Data.Bits hiding (complement)
import Data.List (foldl')

import Control.DeepSeq

import Agda.Utils.Natural

import Debug.Trace

import Prelude hiding (null, foldr, foldl)

-- | Variable sets.
newtype VarSet = VarSet Natural
  -- ^ The actual variable set, stored as the bits of a @'Natural'@.
  --
  -- This exploits the fact that numbers smaller than @0xffffffffffffffff@
  -- are stored within an unboxed machine word in GHC, which means that
  -- most of our operations can be done in a single instruction.
  deriving (Eq, Ord)

instance Show VarSet where
  showsPrec d vs =
    showParen (d > 10) $
    showString "fromList " . shows (toDescList vs)

instance NFData VarSet where
  rnf (VarSet bs) = rnf bs

-- | @(<>)@ is @'union'@
instance Semigroup VarSet where
  (<>) = union

-- | @mempty@ is @'empty'@.
instance Monoid VarSet where
  mempty = empty

--------------------------------------------------------------------------------
-- Construction

-- | The empty variable set.
empty :: VarSet
empty = VarSet 0
{-# INLINE CONLIKE empty #-}

-- | A variable set with only a single entry.
singleton :: Int -> VarSet
singleton i = VarSet (bit i)
{-# INLINE CONLIKE singleton #-}

-- | Construct a set of variables from a list of indices.
fromList :: [Int] -> VarSet
fromList is = VarSet $ foldl' setBit 0 is
{-# INLINE fromList #-}

-- | Construct a variable set that contains the indices @0..n-1@
full :: Int -> VarSet
full n = VarSet (naturalOnes n)
{-# INLINE CONLIKE full #-}

--------------------------------------------------------------------------------
-- Insertion

-- | Insert an index into a variable set.
insert :: Int -> VarSet -> VarSet
insert i (VarSet bs) = VarSet (setBit bs i)
{-# INLINE insert #-}

--------------------------------------------------------------------------------
-- Deletion

-- | Delete an index from a variable set.
delete :: Int -> VarSet -> VarSet
delete i (VarSet bs) = VarSet (clearBit bs i)
{-# INLINE delete #-}

--------------------------------------------------------------------------------
-- Queries

-- | Is this the empty set?
null :: VarSet -> Bool
null (VarSet bs) = naturalIsZero bs
{-# INLINE null #-}

-- | Is a variable a member of a var set?
member :: Int -> VarSet -> Bool
member i (VarSet bs) = testBit bs i
{-# INLINE member #-}

-- | Find the smallest index in the variable set.
lookupMin :: VarSet -> Maybe Int
lookupMin (VarSet n) | naturalIsZero n = Nothing
lookupMin (VarSet n) | otherwise = Just $! naturalCountTrailingZeros n
{-# INLINE lookupMin #-}

-- | The number of entries in the variable set.
size :: VarSet -> Int
size (VarSet bs) = popCount bs
{-# INLINE size #-}

-- | Check if two variable sets are disjoint.
disjoint :: VarSet -> VarSet -> Bool
disjoint (VarSet bs1) (VarSet bs2) = naturalIsZero (bs1 .&. bs2)
{-# INLINE disjoint #-}

--------------------------------------------------------------------------------
-- Combining variable sets

-- | Union two variable sets.
union :: VarSet -> VarSet -> VarSet
union (VarSet bs1) (VarSet bs2) = VarSet (bs1 .|. bs2)
{-# INLINE union #-}

-- | Union a collection of variable sets together.
unions :: Foldable f => f VarSet -> VarSet
unions = foldl' union empty
{-# SPECIALIZE unions :: [VarSet] -> VarSet #-}

intersection :: VarSet -> VarSet -> VarSet
intersection (VarSet bs1) (VarSet bs2) = VarSet (bs1 .&. bs2)
{-# INLINE intersection #-}

-- | Set difference of two variable sets.
difference :: VarSet -> VarSet -> VarSet
difference (VarSet bs1) (VarSet bs2) = VarSet (naturalAndNot bs1 bs2)
{-# INLINE difference #-}

-- | Infix operator for 'difference'.
(\\) :: VarSet -> VarSet -> VarSet
(\\) = difference

infixl 9 \\

-- | Take a relative complement of a variable set.
complement :: Int -> VarSet -> VarSet
complement n vs = full n \\ vs
{-# INLINE complement #-}

-- | @isSubsetOf vs1 vs2@ determines if @vs1@ is a subset of @vs2@.
isSubsetOf :: VarSet -> VarSet -> Bool
isSubsetOf (VarSet bs1) (VarSet bs2) = (bs1 .&. bs2) == bs1
{-# INLINE isSubsetOf #-}

--------------------------------------------------------------------------------
-- Filters

-- | Split a variable set into elements that are strictly smaller than
-- @n@ and elements that are strictly larger.
split :: Int -> VarSet -> (VarSet, VarSet)
split n vs =
  (intersection vs (full n), difference vs (full (n + 1)))

--------------------------------------------------------------------------------
-- Folds

-- | Fold over the elements of a variable set in descending order.
foldr :: (Int -> a -> a) -> a -> VarSet -> a
foldr f a (VarSet bs) = naturalFoldrBits f a bs
{-# NOINLINE foldr #-}

-- | Fold over the elements of a variable set in ascending order.
foldl :: (a -> Int -> a) -> a -> VarSet -> a
foldl f a (VarSet bs) = naturalFoldlBits f a bs
{-# NOINLINE foldl #-}

--------------------------------------------------------------------------------
-- Views

-- | Retrieve the smallest index in the variable set along with the set sans that
-- element, or 'Nothing' if the set was empty.
minView :: VarSet -> Maybe (Int, VarSet)
minView vs = do
  i <- lookupMin vs
  pure (i, delete i vs)

--------------------------------------------------------------------------------
-- Contextual operations

-- | Remove the first @n@ entries from the variable set,
-- and shift the indices of all other entries down by @n@.
strengthen :: Int -> VarSet -> VarSet
strengthen n (VarSet bs) = VarSet (bs `shiftR` n)
{-# INLINE strengthen #-}

-- | Shift all indices in the variable set up by @n@.
weaken :: Int -> VarSet -> VarSet
weaken n (VarSet bs) = VarSet (bs `shiftL` n)
{-# INLINE weaken #-}

--------------------------------------------------------------------------------
-- Conversions

-- | Convert a variable set to a descending list of indices.
toDescList :: VarSet -> [Int]
toDescList = foldr (:) []
{-# INLINE toDescList #-}

-- | Convert a variable set to an ascending list of indices.
toAscList :: VarSet -> [Int]
toAscList = foldl (flip (:)) []
{-# INLINE toAscList #-}

--------------------------------------------------------------------------------
-- Debugging

-- | Trace the size of a variable set to the eventlog.
traceVarSetSize :: VarSet -> VarSet
traceVarSetSize vs@(VarSet bs) =
  traceEvent ("VarSet.size=" <> show (naturalSizeWords bs)) vs

{-|
Manage sets of natural numbers (de Bruijn indices).

This file contains an implementation of finite sets of integers
that is optimized for storing sets of free variables. Notably
de Bruijn indices/levels are not uniformly distributed across the
range of 'Int', and are typically very small (EG: smaller than 64).
This makes @IntSet@ somewhat ill-suited for the task: it is designed
to perform well for values across the entire range of 'Int', at the
cost of lots of pointer indirections and poor memory locality.

Instead, 'VarSet' stores free variables as a bit-vector. When the
elements in the set are all smaller than 64, we can fit the entire set
into a single unboxed 'Word#', which makes most of our set operations
a single instruction.

When we exceed this bound, we fall back to an unboxed 'ByteArray#'. Though
not as fast as the happy path, this has good memory locality, and
we can still implement our set operations using bitwise ops.
-}

module Agda.Utils.VarSet
  ( VarSet(..)
  -- $varSetConstruct
  , empty
  , singleton
  , fromList
  , all
  -- $varSetInsertion
  , insert
  -- $varSetDeletion
  , delete
  -- $varSetQuery
  , null
  , member
  , lookupMin
  , size
  , disjoint
  , isSubsetOf
  -- $varSetCombine
  , union
  , unions
  , intersection
  , difference
  , (\\)
  -- $varSetFilter
  , split
  -- $varSetFolds
  , foldr
  -- $varSetViews
  , minView
  -- $varSetContextual
  , strengthen
  , weaken
  -- $varSetConversions
  , toDescList
  , toAscList
  )
  where


import Data.Bits

import Control.DeepSeq

import Agda.Utils.Natural
import qualified Agda.Utils.Null as Null
import qualified Agda.Utils.Singleton as Singleton

import Debug.Trace

import Prelude hiding (null, foldr, foldl, all)

-- | Variable sets.
newtype VarSet = VarSet Natural
  -- ^ The actual variable set, stored as the bits of a @'Natural'@.
  --
  -- This exploits the fact that numbers smaller than @'0xffffffffffffffff'@
  -- are stored within an unboxed machine word in GHC, which means that
  -- most of our operations can be done in a single instruction.
  deriving (Eq, Ord)

instance Show VarSet where
  showsPrec d vs =
    showParen (d > 10) $
    showString "fromList " . shows (toDescList vs)

instance NFData VarSet where
  -- All fields of @VarSet@ are strict so it suffices to force the constructor.
  rnf (VarSet n) = ()

-- | @(<>)@ is @'union'@
instance Semigroup VarSet where
  (<>) = union

-- | @mempty@ is @'empty'@.
instance Monoid VarSet where
  mempty = empty

instance Null.Null VarSet where
  empty = empty

instance Singleton.Singleton Int VarSet where
  singleton = singleton

-- * Construction
--
-- $varSetConstruct

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
fromList is = VarSet $ (foldl' setBit 0) is
{-# INLINE fromList #-}

-- | Construct a variable set that contains the indices @0..n-1@
all :: Int -> VarSet
all n = VarSet (2 ^ n - 1)
{-# INLINE CONLIKE all #-}

-- * Insertion
--
-- $varSetInsertion

-- | Insert an index into a variable set.
insert :: Int -> VarSet -> VarSet
insert i (VarSet bs) = VarSet (setBit bs i)
{-# INLINE insert #-}

-- * Deletion
--
-- $varSetDeletion

-- | Delete an index from a variable set.
delete :: Int -> VarSet -> VarSet
delete i (VarSet bs) = VarSet (clearBit bs i)
{-# INLINE delete #-}

-- * Queries
--
-- $varSetQuery

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
lookupMin (VarSet n) | otherwise = Just $ naturalCountTrailingZeros n

-- | The number of entries in the variable set.
size :: VarSet -> Int
size (VarSet bs) = popCount bs
{-# INLINE size #-}

-- | Check if two variable sets are disjoint.
disjoint :: VarSet -> VarSet -> Bool
disjoint (VarSet bs1) (VarSet bs2) = naturalIsZero (bs1 .&. bs2)
{-# INLINE disjoint #-}

-- * Combining variable sets
--
-- $varSetCombine

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

-- | @isSubsetOf vs1 vs2@ determines if @vs1@ is a subset of @vs2@.
isSubsetOf :: VarSet -> VarSet -> Bool
isSubsetOf (VarSet bs1) (VarSet bs2) = (bs1 .&. bs2) == bs1
{-# INLINE isSubsetOf #-}

-- * Filters
--
-- $varSetFilter

-- | Split a variable set into elements that are strictly smaller than
-- @n@ and elements that are strictly larger.
split :: Int -> VarSet -> (VarSet, VarSet)
split n vs =
  (intersection vs (all n), difference vs (all (n + 1)))


-- * Folds
--
-- $varSetFolds

-- | Fold over the elements
foldr :: (Int -> a -> a) -> a -> VarSet -> a
foldr f a (VarSet bs) = naturalFoldrBits f a bs

foldl :: (a -> Int -> a) -> a -> VarSet -> a
foldl f a (VarSet bs) = naturalFoldlBits f a bs

-- * Views
--
-- $varSetView

-- | Retrieve the smallest index in the variable set along with the set sans that
-- element, or 'Nothing' if the set was empty.
minView :: VarSet -> Maybe (Int, VarSet)
minView vs = do
  i <- lookupMin vs
  pure (i, delete i vs)

-- * Contextual operations
--
-- $varSetContextual

-- | Remove the first @n@ entries from the variable set,
-- and shift the indices of all other entries down by @n@.
strengthen :: Int -> VarSet -> VarSet
strengthen n (VarSet bs) = VarSet (bs `shiftR` n)
{-# INLINE strengthen #-}

-- | Shift all indices in the variable set up by @n@.
weaken :: Int -> VarSet -> VarSet
weaken n (VarSet bs) = VarSet (bs `shiftL` n)
{-# INLINE weaken #-}

-- * Converting variable sets to other datastructures
--
-- $varSetConversions

-- | Convert a variable set to a descending list of indices.
toDescList :: VarSet -> [Int]
toDescList = foldr (:) []
{-# INLINE toDescList #-}

-- | Convert a variable set to an ascending list of indices.
toAscList :: VarSet -> [Int]
toAscList = foldl (flip (:)) []
{-# INLINE toAscList #-}

-- * Debugging

-- | Trace the size of a variable set to the eventlog.
traceVarSetSize :: VarSet -> VarSet
traceVarSetSize = traceEventWith \(VarSet bs) ->
  "VarSet.size=" <> show (naturalSizeWords bs)

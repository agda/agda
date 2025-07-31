-- Needed to get haddock to pick up on identifiers with a #.
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE CPP #-}

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

Instead, 'VarSet' stores free variables as a bitvector. When the
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
  (
  -- * VarSet type
  --
  -- $varSetType
    VarSet(..)
  -- * Construction
  , empty
  , singleton
  , fromList
  , fromDescList
  , full
  , range
  -- * Insertion
  , insert
  , inserts
  , insertsDesc
  -- * Deletion
  , delete
  -- * Queries
  , null
  , member
  , lookupMin
  , lookupMax
  , size
  , disjoint
  , isSubsetOf
  , inRange
  -- * Combining variable sets
  , union
  , unions
  , intersection
  , difference
  , (\\)
  , complement
  -- * Filters
  , split
  , filterLT
  , filterLE
  , filterGT
  , filterGE
  -- * Folds
  --
  -- $varSetFolds
  , foldr
  , foldl
  , foldr'
  , foldl'
  -- * Views
  , minView
  , maxView
  -- * Contextual operations
  , strengthen
  , weaken
  -- * Conversions
  , toDescList
  , toAscList
  )
  where

-- We need the machines word size for some bitwise operations.
#include "MachDeps.h"

import Control.DeepSeq
import Control.Monad

import Data.Binary
import Data.Binary.Get
import Data.Binary.Put
import qualified Data.ByteString as BS
import qualified Data.Foldable as Fold
import Data.Hashable

import GHC.Base hiding (empty, foldr)
import GHC.Num.BigNat
import GHC.Num.WordArray

import Debug.Trace

import Prelude (Num(..), Show(..))
import qualified Prelude as P

import Agda.Utils.ByteArray
import Agda.Utils.Word

-- $varSetType
-- = Invariants
-- A variable set whose maximum entry is less than than 64 is always encoded
-- via the 'VS#' constructor.
-- The final word of a 'VB#' is always non-zero.
--
-- = Performance
-- GHC will use pointer-tagging for datatypes with less than 4 constructors
-- on 32 bit machines (8 on 64 bit), which means that 'VarSet' will be laid
-- out as a tagged pointer to a word-sized piece of data.
--
-- We also pay attention to the constructor ordering here.
-- GHC will lay out the machine code for case statements in
-- reverse order of the datatypes constructors. Both ARM and x86 statically
-- predict that forward branches are not taken, so putting 'VB#' before
-- 'VS#' means that we can eek out a few extra drops of performance.
--
-- Finally, many functions in this module follow the following pattern:
-- @
-- union :: VarSet -> VarSet -> VarSet
-- union (VS# w1) (VS# w2) = VS# (w1 `or#` w2)
-- union vs1 vs2 = unionSlow vs1 vs2
-- {-# INLINE union #-}
--
-- unionSlow :: VarSet -> VarSet -> VarSet
-- unionSlow (VS# w1) (VS# w2) = VS# (w1 `or#` w2)
-- unionSlow (VS# w1) (VB# bs2) = VB# (bigNatOrWord# bs2 w1)
-- unionSlow (VB# bs1) (VS# w2) = VB# (bigNatOrWord# bs1 w2)
-- unionSlow (VB# bs1) (VB# bs2) = VB# (bigNatOr bs1 bs2)
-- {-# NOINLINE unionSlow #-}
-- @
--
-- This makes the 0.0001% of slow cases notably worse, but makes the
-- happy path approximately 3x faster for things like 'inRange', as
-- GHC is able to coalesce all of the happy paths.

-- | A set of de Bruijn indicies/levels.
data VarSet
  = VB# ByteArray#
  -- ^ A variable set whose maximum entry is greater than or equal to 64.
  | VS# Word#
  -- ^ A small variable set whose maximum entry is less than than 64.

-- | Convert a 'ByteArray#' to a variable set, upholding
-- the invariant that all word-sized variable sets should use
-- 'VS#'.
byteArrayToVarSet# :: ByteArray# -> VarSet
byteArrayToVarSet# bs =
  case bigNatSize# bs of
    0# -> empty -- Dont allocate if we don't have to.
    1# -> VS# (indexWordArray# bs 0#)
    _  -> VB# bs

instance Eq VarSet where
  (VS# xs) == (VS# ys) = isTrue# (xs `eqWord#` ys)
  (VB# _) == (VS# _) = False
  (VS# _) == (VB# _) = False
  (VB# xs) == (VB# ys) = bigNatEq xs ys

instance Ord VarSet where
  compare (VS# xs) (VS# ys) = compareWord# xs ys
  compare (VB# _) (VS# _) = GT
  compare (VS# _) (VB# _) = LT
  compare (VB# xs) (VB# ys) = bigNatCompare xs ys

instance P.Show VarSet where
  -- Use the same direction as the 'Show' instance for 'IntSet'.
  showsPrec d vs =
    P.showParen (d > 10) $
    P.showString "fromList " . P.shows (toAscList vs)

instance NFData VarSet where
  rnf (VS# _) = ()
  rnf (VB# _) = ()

-- | @(<>)@ is @'union'@
instance Semigroup VarSet where
  (<>) = union

-- | @mempty@ is @'empty'@.
instance Monoid VarSet where
  mempty = empty

-- This instances is a bit suboptimal.
-- Ideally, 'hashWithSalt' should directly just call an unboxed 'mixHash' when we have a 'VS#',
-- but 'Hashable' doesn't expose enough of its internals for this.
instance Hashable VarSet where
  hash (VS# w) = I# (word2Int# w)
  hash (VB# bs) = hashByteArray bs 0 (I# (sizeofByteArray# bs))

  hashWithSalt salt (VS# w)  = hashWithSalt (I# (word2Int# w)) salt
  hashWithSalt salt (VB# bs) = hashByteArrayWithSalt bs 0 (I# (sizeofByteArray# bs)) salt

-- Could be much more efficient. Ideally, we would just have our hands
-- on a pointer and an offset, but 'Binary' doesn't give a nice interface
-- for this.
instance Binary VarSet where
  put (VS# w) = putWord8 0 <> put (W# w)
  put (VB# bs) = putWord8 1 <> put (I# len) <> loop (len -# 1#)
    where
      len = bigNatSize# bs

      loop :: Int# -> Put
      loop i =
        if isTrue# (i >=# 0#) then
          put (W# (indexWordArray# bs i)) <> loop (i -# 1#)
        else
          mempty

  get = do
    tag <- get @Word8
    case tag of
      0 -> do
        W# w <- get @Word
        pure (VS# w)
      _ -> do
        -- This is quite bad, but we don't have very good tools for
        -- doing this efficiently. This should really never happen
        -- though, so it's not the end of the world.
        len <- get @Int
        words <- replicateM len (get @Word)
        pure (VB# (bigNatFromWordList words))

--------------------------------------------------------------------------------
-- Construction

-- | The empty variable set.
empty :: VarSet
empty = VS# 0##
{-# INLINE CONLIKE empty #-}

-- | A variable set with only a single entry.
singleton :: Int -> VarSet
singleton (I# i) =
  if isTrue# (i <# WORD_SIZE_IN_BITS#) then
    VS# (uncheckedBitWord# i)
  else
    VB# (bigNatBit# (int2Word# i))
{-# INLINE singleton #-}

-- | Construct a set of variables from a list of indices.
fromList :: [Int] -> VarSet
fromList is = inserts is empty
{-# INLINE fromList #-}

-- | Construct a set of variables from a list of indices sorted in descending order.
-- This can be more efficient than 'fromList', as we only need to perform a single
-- to determine that elements of the list are smaller than 64.
--
-- The precondition that the variables are sorted in descending order is
-- not checked by 'fromDescList'.
fromDescList :: [Int] -> VarSet
fromDescList is = insertsDesc is empty

-- | Construct a variable set that contains the indices @[0..n-1]@.
full :: Int -> VarSet
full (I# n) =
  if isTrue# (n <=# 0#) then
    empty
  else if isTrue# (n <# WORD_SIZE_IN_BITS#) then
    VS# (uncheckedWordOnes# n)
  else
    VB# (byteArrayOnes# n)
{-# INLINE full #-}

-- | Construct a variable set that contains the indices @[lo+1..hi-1]@.
range :: Int -> Int -> VarSet
range lo hi =
  -- Most of the time, @hi@ is the length of the context
  -- and @lo@ is some variable, so it would be a waste of time
  -- to try and avoid work by checking if hi <= lo.
  full hi \\ full (lo + 1)
{-# INLINE range #-}

--------------------------------------------------------------------------------
-- Insertion

-- | Insert an index into a variable set.
insert :: Int -> VarSet -> VarSet
insert (I# i) (VS# w) =
  if isTrue# (i <# WORD_SIZE_IN_BITS#) then
    VS# (uncheckedSetBitWord# w i)
  else
    VB# (bigNatSetBit# (bigNatFromWord# w) (int2Word# i))
insert (I# i) (VB# bs) = VB# (bigNatSetBit# bs (int2Word# i))
{-# INLINE insert #-}

-- | Insert a list of variables into a @VarSet@.
inserts :: [Int] -> VarSet -> VarSet
inserts xs vs = Fold.foldl' (flip insert) vs xs

-- | Insert a list of variables sorted in descending order into a 'VarSet'.
-- This can be more efficient than 'inserts', as we only need to perform a single
-- to determine that elements of the list are smaller than 64.
--
-- The precondition that the variables are sorted in descending order is
-- not checked by 'insertsDesc'.
insertsDesc :: [Int] -> VarSet -> VarSet
insertsDesc [] vs = vs
insertsDesc (I# x:xs) (VS# w) | isTrue# (x <# WORD_SIZE_IN_BITS#) = VS# (insertsDescFast# xs (uncheckedSetBitWord# w x))
insertsDesc xs vs = inserts xs vs -- Could be more optimal but this is basically never taken.

-- | Fast path for 'insertsDesc' that omits bounds checking.
insertsDescFast# :: [Int] -> Word# -> Word#
insertsDescFast# [] w = w
insertsDescFast# (I# x:xs) w = insertsDescFast# xs (uncheckedSetBitWord# w x)

--------------------------------------------------------------------------------
-- Deletion

-- | Delete an index from a variable set.
delete :: Int -> VarSet -> VarSet
delete (I# i) vs@(VS# w) =
  if isTrue# (i <# WORD_SIZE_IN_BITS#) then
    VS# (uncheckedClearBitWord# w i)
  else
    vs
delete (I# i) (VB# vs) = byteArrayToVarSet# (bigNatClearBit# vs (int2Word# i))
{-# INLINE delete #-}

--------------------------------------------------------------------------------
-- Queries

-- | Is this the empty set?
null :: VarSet -> Bool
null (VS# 0##) = True
null _ = False
{-# INLINE null #-}

-- | Is a variable a member of a var set?
member :: Int -> VarSet -> Bool
member (I# i) (VS# w) = isTrue# ((0# <=# i) `andI#` (i <# WORD_SIZE_IN_BITS#) `andI#` (uncheckedTestBitWord# w i))
member (I# i) (VB# bs) = isTrue# (bigNatTestBit# bs (int2Word# i))
{-# INLINE member #-}

-- | Find the smallest index in the variable set.
lookupMin :: VarSet -> Maybe Int
lookupMin (VS# w) =
  if isTrue# (w `eqWord#` 0##) then
    Nothing
  else
    Just (I# (word2Int# (lowestBitWord# w)))
lookupMin (VB# bs) = Just (I# (lookupMinSlow# 0# bs))
{-# INLINE lookupMin #-}

-- | Slow path for 'lookupMin'.
lookupMinSlow# :: Int# -> ByteArray# -> Int#
lookupMinSlow# i bs =
  -- We don't need to check if the index goes out of bounds, as we know that
  -- 0 always gets stored as an @VS#@, so there must be *some* set bit.
  let w = indexWordArray# bs i in
  if isTrue# (eqWord# w 0##) then
    lookupMinSlow# (i +# 1#) bs
  else
    WORD_SIZE_IN_BITS# *# i +# (word2Int# (lowestBitWord# w))
{-# NOINLINE lookupMinSlow# #-}

-- | Find the largest index in the variable set.
lookupMax :: VarSet -> Maybe Int
lookupMax (VS# w) =
  if isTrue# (w `eqWord#` 0##) then
    Nothing
  else
    Just (I# (word2Int# (highestBitWord# w)))
lookupMax (VB# bs) =
  -- We know that the highest bit must be in the final word of 'bs',
  -- as there are no leading 0 words in our varsets.
  let len = wordArraySize# bs
  in Just (I# (word2Int# (highestBitWord# (indexWordArray# bs (len -# 1#)))))
{-# INLINE lookupMax #-}

-- | The number of entries in the variable set.
size :: VarSet -> Int
size (VS# w) = I# (word2Int# (popCnt# w))
size (VB# bs) = I# (word2Int# (bigNatPopCount# bs))
{-# INLINE size #-}

-- | Check if two variable sets are disjoint.
disjoint :: VarSet -> VarSet -> Bool
disjoint (VS# w1) (VS# w2) = isTrue# (disjointWord# w1 w2)
disjoint vs1 vs2 = isTrue# (disjointSlow# vs1 vs2)
{-# INLINE disjoint #-}

-- | Slow path for 'disjoint'.
disjointSlow# :: VarSet -> VarSet -> Int#
disjointSlow# (VS# w1) (VS# w2) = disjointWord# w1 w2
disjointSlow# (VB# bs1) (VS# w2) = disjointWord# (indexWordArray# bs1 0#) w2
disjointSlow# (VS# w1) (VB# bs2) = disjointWord# (indexWordArray# bs2 0#) w1
disjointSlow# (VB# bs1) (VB# bs2) = byteArrayDisjoint# bs1 bs2
{-# NOINLINE disjointSlow# #-}

--------------------------------------------------------------------------------
-- Combining variable sets

-- | Union two variable sets.
union :: VarSet -> VarSet -> VarSet
union (VS# w1) (VS# w2) = VS# (w1 `or#` w2)
union vs1 vs2 = unionSlow vs1 vs2
{-# INLINE union #-}

-- | Slow path for 'union'.
unionSlow :: VarSet -> VarSet -> VarSet
unionSlow (VS# w1) (VS# w2) = VS# (w1 `or#` w2)
unionSlow (VS# w1) (VB# bs2) = VB# (bigNatOrWord# bs2 w1)
unionSlow (VB# bs1) (VS# w2) = VB# (bigNatOrWord# bs1 w2)
unionSlow (VB# bs1) (VB# bs2) = VB# (bigNatOr bs1 bs2)
{-# NOINLINE unionSlow #-}

-- | Union a collection of variable sets together.
unions :: P.Foldable f => f VarSet -> VarSet
unions = Fold.foldl' union empty
{-# SPECIALIZE unions :: [VarSet] -> VarSet #-}

-- | Take the intersection of two variable sets.
intersection :: VarSet -> VarSet -> VarSet
intersection (VS# w1) (VS# w2) = VS# (w1 `and#` w2)
intersection vs1 vs2 = intersectionSlow vs1 vs2
{-# INLINE intersection #-}

-- | Slow path for 'intersection'.
intersectionSlow :: VarSet -> VarSet -> VarSet
intersectionSlow (VS# w1) (VS# w2) = VS# (w1 `and#` w2)
intersectionSlow (VS# w1) (VB# bs2) = VS# (w1 `and#` indexWordArray# bs2 0#)
intersectionSlow (VB# bs1) (VS# w2) = VS# (indexWordArray# bs1 0# `and#` w2)
intersectionSlow (VB# bs1) (VB# bs2) = VB# (bigNatAnd bs1 bs2)
{-# NOINLINE intersectionSlow #-}

-- | Set difference of two variable sets.
difference :: VarSet -> VarSet -> VarSet
difference (VS# w1) (VS# w2) = VS# (w1 `andNot#` w2)
difference vs1 vs2 = differenceSlow vs1 vs2
{-# INLINE difference #-}

-- | Slow path for 'difference'.
differenceSlow :: VarSet -> VarSet -> VarSet
differenceSlow (VS# w1) (VS# w2) = VS# (w1 `andNot#` w2)
differenceSlow (VS# w1) (VB# bs2) = VS# (w1 `andNot#` indexWordArray# bs2 0#)
differenceSlow (VB# bs1) (VS# w2) = VB# (bigNatAndNotWord# bs1 w2)
differenceSlow (VB# bs1) (VB# bs2) = byteArrayToVarSet# (bigNatAndNot bs1 bs2)
{-# NOINLINE differenceSlow #-}

-- | Infix operator for 'difference'.
(\\) :: VarSet -> VarSet -> VarSet
(\\) = difference
{-# INLINE (\\) #-}

-- | Take a relative complement of a variable set.
complement :: Int -> VarSet -> VarSet
complement n vs = full n \\ vs
{-# INLINE complement #-}

-- | @isSubsetOf vs1 vs2@ determines if @vs1@ is a subset of @vs2@.
isSubsetOf :: VarSet -> VarSet -> Bool
isSubsetOf (VS# w1) (VS# w2) = isTrue# ((w1 `and#` w2) `eqWord#` w1)
isSubsetOf vs1 vs2 = isTrue# (isSubsetOfSlow# vs1 vs2)
{-# INLINE isSubsetOf #-}

-- | Slow path for 'isSubsetOf'.
isSubsetOfSlow# :: VarSet -> VarSet -> Int#
isSubsetOfSlow# (VS# w1) (VS# w2) = (w1 `and#` w2) `eqWord#` w1
isSubsetOfSlow# (VS# w1) (VB# bs2) = (w1 `and#` indexWordArray# bs2 0#) `eqWord#` w1
isSubsetOfSlow# (VB# bs1) (VS# w2) = 0#
isSubsetOfSlow# (VB# bs1) (VB# bs2) = byteArrayIsSubsetOf# bs1 bs2
{-# NOINLINE isSubsetOfSlow# #-}

-- | @inRange lo hi vs@ determines if all the variables in @vs@
-- are within the range @[lo+1 .. hi-1]@.
inRange :: Int -> Int -> VarSet -> Bool
inRange lo hi vs =
  -- This might seem inefficient, but is optimal
  -- when @range lo hi@ and @vs@ both fit within a single word.
  vs `isSubsetOf` range lo hi
{-# INLINE inRange #-}

--------------------------------------------------------------------------------
-- Filters

-- | Split a variable set into elements that are strictly smaller than
-- @n@ and elements that are strictly larger.
--
-- Note that this is strict in both components of the pair. If you only
-- need one half, use 'filterLT' or 'filterGT'.
split :: Int -> VarSet -> (VarSet, VarSet)
split n vs =
  let !lo = intersection vs (full n)
      !hi = difference vs (full (n + 1))
  in (lo, hi)

-- | Filter a variable set to elements that are less than to an index.
filterLT :: Int -> VarSet -> VarSet
filterLT n vs = intersection vs (full n)
{-# INLINE filterLT #-}

-- | Filter a variable set to elements that are less than or equal to an index.
filterLE :: Int -> VarSet -> VarSet
filterLE n vs = intersection vs (full (n + 1))
{-# INLINE filterLE #-}

-- | Filter a variable set to elements that are greater than to an index.
filterGT :: Int -> VarSet -> VarSet
filterGT n vs = difference vs (full (n + 1))
{-# INLINE filterGT #-}

-- | Filter a variable set to elements that are greater than or equal to an index.
filterGE :: Int -> VarSet -> VarSet
filterGE n vs = difference vs (full n)
{-# INLINE filterGE #-}

--------------------------------------------------------------------------------
-- Folds

-- $varSetFolds
-- Like most unordered containers, @foldr@ and @foldl@ are somewhat ambigious
-- names for folds over a 'VarSet'. For the sake of consistency, we adopt the
-- same convention as 'Data.IntSet.IntSet', where
-- @
-- VarSet.foldr f x = foldr f x . VarSet.toAscList
-- VarSet.foldl f x = foldl f x . VarSet.toAscList
-- @
--
-- Unfortunately, this convention the opposite of how our sets are laid out
-- in memory.

-- | Lazily fold over the elements of a variable set in ascending order.
foldr :: (Int -> a -> a) -> a -> VarSet -> a
foldr f a (VS# w) = wordFoldrBits# f a w
foldr f a (VB# bs) = byteArrayFoldrBits# f a bs

-- | Lazily fold over the elements of a variable set in descending order.
foldl :: (a -> Int -> a) -> a -> VarSet -> a
foldl f a (VS# w) = wordFoldlBits# f a w
foldl f a (VB# bs) = byteArrayFoldlBits# f a bs

-- | Strictly fold over the elements of a variable set in ascending order.
foldr' :: (Int -> a -> a) -> a -> VarSet -> a
foldr' f a (VS# w) = wordFoldrBitsStrict# f a w
foldr' f a (VB# bs) = byteArrayFoldrBitsStrict# f a bs

-- | Strictly fold over the elements of a variable set in descending order.
foldl' :: (Int -> a -> a) -> a -> VarSet -> a
foldl' f a (VS# w) = wordFoldrBitsStrict# f a w
foldl' f a (VB# bs) = byteArrayFoldrBitsStrict# f a bs


--------------------------------------------------------------------------------
-- Views

-- | Retrieve the smallest index in the variable set along with the set sans that
-- element, or 'Nothing' if the set was empty.
minView :: VarSet -> Maybe (Int, VarSet)
minView vs =
  case lookupMin vs of
    Just i ->
      let !vs' = delete i vs
      in Just (i, vs')
    Nothing -> Nothing

-- | Retrieve the smallest index in the variable set along with the set sans that
-- element, or 'Nothing' if the set was empty.
maxView :: VarSet -> Maybe (Int, VarSet)
maxView vs =
  case lookupMax vs of
    Just i ->
      let !vs' = delete i vs
      in Just (i, vs')
    Nothing -> Nothing

--------------------------------------------------------------------------------
-- Contextual operations

-- | Remove the first @n@ entries from the variable set,
-- and shift the indices of all other entries down by @n@.
strengthen :: Int -> VarSet -> VarSet
strengthen (I# n) (VS# w) =
  -- A strengthening by 64+ will literally never happen, so we are better
  -- off avoiding the branch then we are saving an allocation by
  -- re-using 'empty' when the shift result would be 0.
  VS# (w `shiftRL#` n)
strengthen (I# n) (VB# bs) =
  byteArrayToVarSet# (bigNatShiftR# bs (int2Word# n))
{-# INLINE strengthen #-}

-- | Shift all indices in the variable set up by @n@.
weaken :: Int -> VarSet -> VarSet
weaken (I# n) (VS# w) =
  if isTrue# (clz# w `geWord#` int2Word# n) then
    VS# (w `uncheckedShiftL#` n)
  else
    VB# (bigNatShiftL# (bigNatFromWord# w) (int2Word# n))
weaken (I# n) (VB# bs) =
  VB# (bigNatShiftL# bs (int2Word# n))
{-# INLINE weaken #-}

--------------------------------------------------------------------------------
-- Conversions

-- | Convert a variable set to a descending list of indices.
toDescList :: VarSet -> [Int]
toDescList = foldl (flip (:)) []
{-# INLINE toDescList #-}

-- | Convert a variable set to an ascending list of indices.
toAscList :: VarSet -> [Int]
toAscList = foldr (:) []
{-# INLINE toAscList #-}

--------------------------------------------------------------------------------
-- Debugging

-- | Trace the size of a variable set to the eventlog.
traceVarSetSize :: VarSet -> VarSet
traceVarSetSize vs@(VS# _) = traceEvent ("VarSet.size=1") vs
traceVarSetSize vs@(VB# bs) = traceEvent ("VarSet.size=" <> show (bigNatSize bs)) vs

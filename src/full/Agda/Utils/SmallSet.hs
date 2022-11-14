-- | Small sets represented as immutable bit arrays for fast membership checking.
--
-- Membership checking is O(1), but all other operations are O(n)
-- where n is the size of the element type.
-- The element type needs to implement 'Bounded' and 'Ix'.
--
-- Mimics the interface of 'Data.Set'.
--
-- Import as:
-- @
--    import qualified Agda.Utils.SmallSet as SmallSet
--    import Agda.Utils.SmallSet (SmallSet)
-- @

module Agda.Utils.SmallSet
  ( SmallSet()
  , Ix
  , (\\)
  , complement
  , delete
  , difference
  , elems
  , empty
  , fromList, fromAscList, fromDistinctAscList
  , insert
  , intersection
  , isSubsetOf
  , mapMembership
  , member
  , notMember
  , null
  , singleton
  , toList, toAscList
  , total
  , union
  , zipMembershipWith
  ) where

import Prelude hiding (null)

import Control.DeepSeq

import Data.Array.IArray (Ix, Array)
import qualified Data.Array.IArray as Array

-- Note: we might want to use unboxed arrays, but they have no Data instance
--
-- Update: There is currently no need for a Data instance. An attempt
-- was made to replace Array with Data.Array.Unboxed.UArray. Limited
-- testing suggested that this does not make much of a difference in
-- practice (at least not when it comes to type-checking the standard
-- library up to and including Data.Nat, with Agda compiled without
-- -foptimise-heavily).

-- | Let @n@ be the size of type @a@.
type SmallSetElement a = (Bounded a, Ix a)
newtype SmallSet a = SmallSet { theSmallSet :: Array a Bool }
  deriving (Eq, Ord, Show, NFData)

-- * Query

-- | Time O(n)!
null :: SmallSetElement a => SmallSet a -> Bool
null = all (== False) . Array.elems . theSmallSet

-- | Time O(1).
member :: SmallSetElement a => a -> SmallSet a -> Bool
member a s = theSmallSet s Array.! a

-- | @not . member a@.  Time O(1).
notMember :: SmallSetElement a => a -> SmallSet a -> Bool
notMember a = not . member a

-- | Time O(n).
isSubsetOf ::  SmallSetElement a => SmallSet a -> SmallSet a -> Bool
isSubsetOf s t = and $ toBoolListZipWith implies s t
  where implies a b = if a then b else True

-- * Construction

-- | The empty set.  Time O(n).
empty :: SmallSetElement a => SmallSet a
empty = fromBoolList (repeat False)

-- | The full set.  Time O(n).
total :: SmallSetElement a => SmallSet a
total = fromBoolList (repeat True)

-- | A singleton set.  Time O(n).
singleton :: SmallSetElement a => a -> SmallSet a
singleton a = fromList [a]

-- | Time O(n).
insert :: SmallSetElement a => a -> SmallSet a -> SmallSet a
insert a = update [(a,True)]

-- | Time O(n).
delete :: SmallSetElement a => a -> SmallSet a -> SmallSet a
delete a = update [(a,False)]

-- * Combine

-- | Time O(n).
complement :: SmallSetElement a => SmallSet a -> SmallSet a
complement = mapMembership not

-- | Time O(n).
difference, (\\) :: SmallSetElement a => SmallSet a -> SmallSet a -> SmallSet a
difference = zipMembershipWith $ \ b c -> b && not c
(\\)       = difference

-- | Time O(n).
intersection ::  SmallSetElement a => SmallSet a -> SmallSet a -> SmallSet a
intersection = zipMembershipWith (&&)

-- | Time O(n).
union ::  SmallSetElement a => SmallSet a -> SmallSet a -> SmallSet a
union = zipMembershipWith (||)

-- | Time O(n).
mapMembership :: SmallSetElement a => (Bool -> Bool) -> SmallSet a -> SmallSet a
mapMembership f = SmallSet . Array.amap f . theSmallSet

-- | Time O(n).
zipMembershipWith :: SmallSetElement a => (Bool -> Bool -> Bool) -> SmallSet a -> SmallSet a -> SmallSet a
zipMembershipWith f s t = fromBoolList $ toBoolListZipWith f s t

-- * Conversion

-- | Time O(n).
elems, toList, toAscList :: SmallSetElement a => SmallSet a -> [a]
elems     = map fst . filter snd . Array.assocs . theSmallSet
toList    = elems
toAscList = elems

-- | Time O(n).
fromList, fromAscList, fromDistinctAscList :: SmallSetElement a => [a] -> SmallSet a
fromList            = flip update empty . map (,True)
fromAscList         = fromList
fromDistinctAscList = fromList

-- * Internal

-- | Time O(n).  Assumes @Bool@-vector of length @n@.
fromBoolList :: SmallSetElement a => [Bool] -> SmallSet a
fromBoolList = SmallSet . Array.listArray (minBound, maxBound)

-- | Time O(n).  Produces @Bool@-vector of length @n@.
toBoolList :: SmallSetElement a => SmallSet a -> [Bool]
toBoolList = Array.elems . theSmallSet

-- | Time O(n).  Produces @Bool@-vector of length @n@.
toBoolListZipWith :: SmallSetElement a => (Bool -> Bool -> Bool) -> SmallSet a -> SmallSet a -> [Bool]
toBoolListZipWith f s t = zipWith f (toBoolList s) (toBoolList t)

-- | Time O(n).  Bulk insert/delete.
update :: SmallSetElement a => [(a,Bool)] -> SmallSet a -> SmallSet a
update u s = SmallSet $ theSmallSet s Array.// u

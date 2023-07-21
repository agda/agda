-- | Small sets represented as a bitmask for fast membership checking.
--
-- With the exception of converting to/from lists, all operations are O(1).
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
  , SmallSetElement
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
  , member
  , notMember
  , null
  , singleton
  , toList, toAscList
  , total
  , union
  ) where

import Prelude hiding (null)

import Control.DeepSeq

import Data.Word (Word64)
import Data.List (foldl')
import Data.Bits hiding (complement)
import qualified Data.Bits as Bits
import Data.Ix

import qualified Agda.Utils.Null as Null

-- | An element in a small set.
--
-- This must implement 'Bounded' and 'Ix', and contain at most 64 values.
class (Bounded a, Ix a) => SmallSetElement a where

newtype SmallSet a = SmallSet { theSmallSet :: Word64 }
  deriving (Eq, Ord, Show, NFData)


instance SmallSetElement a => Null.Null (SmallSet a) where
  empty = empty
  null = null

instance SmallSetElement a => Semigroup (SmallSet a) where
  (<>) = union

instance SmallSetElement a => Monoid (SmallSet a) where
  mempty = empty

-- * Query

-- | Time O(1).
null :: SmallSetElement a => SmallSet a -> Bool
null s = theSmallSet s == 0

-- | Time O(1).
member :: SmallSetElement a => a -> SmallSet a -> Bool
member a s = theSmallSet s `testBit` idx a

-- | @not . member a@.  Time O(1).
notMember :: SmallSetElement a => a -> SmallSet a -> Bool
notMember a = not . member a

-- * Construction

-- | The empty set.  Time O(1).
empty :: SmallSetElement a => SmallSet a
empty = SmallSet 0

-- | The full set.  Time O(1).
total :: forall a. SmallSetElement a => SmallSet a
total = SmallSet $ Bits.complement 0

-- | A singleton set.  Time O(1).
singleton :: SmallSetElement a => a -> SmallSet a
singleton a = SmallSet $ bit (idx a)

-- | Time O(1).
insert :: SmallSetElement a => a -> SmallSet a -> SmallSet a
insert a s = SmallSet $ theSmallSet s `setBit` idx a

-- | Time O(1).
delete :: SmallSetElement a => a -> SmallSet a -> SmallSet a
delete a s = SmallSet $ theSmallSet s `clearBit` idx a

-- * Combine

-- | Time O(n).
complement :: SmallSetElement a => SmallSet a -> SmallSet a
complement = SmallSet . Bits.complement . theSmallSet

-- | Time O(1).
difference, (\\) :: SmallSetElement a => SmallSet a -> SmallSet a -> SmallSet a
difference s t = SmallSet $ theSmallSet s .&. Bits.complement (theSmallSet t)
(\\)       = difference

-- | Time O(1).
intersection ::  SmallSetElement a => SmallSet a -> SmallSet a -> SmallSet a
intersection s t = SmallSet $ theSmallSet s .&. theSmallSet t

-- | Time O(n).
union ::  SmallSetElement a => SmallSet a -> SmallSet a -> SmallSet a
union s t = SmallSet $ theSmallSet s .|. theSmallSet t

-- * Conversion

-- | Time O(n).
elems, toList, toAscList :: SmallSetElement a => SmallSet a -> [a]
elems s   = filter (\i -> theSmallSet s `testBit` idx i) (range bounds)
toList    = elems
toAscList = elems

-- | Time O(n).
fromList, fromAscList, fromDistinctAscList :: SmallSetElement a => [a] -> SmallSet a
fromList            = foldl' (flip insert) empty
fromAscList         = fromList
fromDistinctAscList = fromList

-- * Internals

bounds :: SmallSetElement a => (a, a)
bounds = (minBound, maxBound)

idx :: SmallSetElement a => a -> Int
idx a = index bounds a

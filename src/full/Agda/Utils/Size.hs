-- | Collection size.
--
--   For 'TermSize' see "Agda.Syntax.Internal".

module Agda.Utils.Size
  ( Sized(..)
  , SizedThing(..)
  , sizeThing
  , module X
  ) where

import Prelude hiding (null, length)

import Data.Peano as X     ( Peano(Zero,Succ) )
import Data.Foldable       (Foldable, length)
import Data.HashMap.Strict (HashMap)
import Data.HashSet        (HashSet)
import Data.IntMap         (IntMap)
import Data.IntSet         (IntSet)
import qualified Data.IntSet as IntSet
import Data.Map            (Map)
import Data.Set            (Set)
import Data.Sequence       (Seq)

import Agda.Utils.List1    (List1)
import Agda.Utils.Null

-- | The size of a collection (i.e., its length).

class Sized a where
  -- | Strict size computation.
  --
  -- Anti-patterns: @size xs == n@ where @n@ is @0@, @1@ or another number
  -- that is likely smaller than @size xs@.
  -- Similar for @size xs >= 1@ etc.
  -- Use 'natSize' instead.
  --
  -- See https://wiki.haskell.org/Haskell_programming_tips#Don.27t_ask_for_the_length_of_a_list_when_you_don.27t_need_it .
  size :: a -> Int

  default size :: (Foldable t, t b ~ a) => a -> Int
  size = length

  -- | Lazily compute a (possibly infinite) size.
  --
  -- Use when comparing a size against a fixed number.
  natSize :: a -> Peano

  default natSize :: (Foldable t, t b ~ a) => a -> Peano
  natSize = foldr (const Succ) Zero

instance Sized [a]
instance Sized (Set a)
instance Sized (HashMap k a)
instance Sized (HashSet a)
instance Sized (IntMap a)
instance Sized (List1 a)
instance Sized (Map k a)
instance Sized (Seq a)
instance Sized IntSet where
  size = IntSet.size
  natSize = toEnum . size

-- | Thing decorated with its size.
--   The thing should fit into main memory, thus, the size is an @Int@.

data SizedThing a = SizedThing
  { theSize    :: !Int
  , sizedThing :: a
  }

-- | Cache the size of an object.
sizeThing :: Sized a => a -> SizedThing a
sizeThing a = SizedThing (size a) a

-- | Return the cached size.
instance Sized (SizedThing a) where
  size = theSize
  natSize = toEnum . theSize

instance Null a => Null (SizedThing a) where
  empty = SizedThing 0 empty
  null  = null . sizedThing

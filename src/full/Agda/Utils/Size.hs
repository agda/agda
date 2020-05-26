-- | Collection size.
--
--   For 'TermSize' see "Agda.Syntax.Internal".

{-# LANGUAGE TypeFamilies #-}  -- for type equality ~

module Agda.Utils.Size
  ( Sized(..)
  , SizedThing(..)
  , sizeThing
  ) where

import Prelude hiding (null, length)

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
  size :: a -> Int

  default size :: (Foldable t, t b ~ a) => a -> Int
  size = length

instance Sized [a]
instance Sized (Set a)
instance Sized (HashMap k a)
instance Sized (HashSet a)
instance Sized (IntMap a)
instance Sized (List1 a)
instance Sized (Map k a)
instance Sized (Seq a)
instance Sized IntSet where size = IntSet.size

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

instance Null a => Null (SizedThing a) where
  empty = SizedThing 0 empty
  null  = null . sizedThing

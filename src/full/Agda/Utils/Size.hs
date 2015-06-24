-- | Collection size.
--
--   For 'TermSize' see "Agda.Syntax.Internal".

module Agda.Utils.Size
  ( Sized(..)
  , SizedThing(..)
  , sizeThing
  ) where

import Prelude hiding (null)

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.List as List

import Agda.Utils.Null

-- | The size of a collection (i.e., its length).
--
--   Should fit into an @Int@.  TODO: change to @Int@.

class Sized a where
  size :: Integral n => a -> n

instance Sized [a] where
  size = List.genericLength

instance Sized (IntMap a) where
  size = fromIntegral . IntMap.size

instance Sized IntSet where
  size = fromIntegral . IntSet.size

instance Sized (Map k a) where
  size = fromIntegral . Map.size

instance Sized (Set a) where
  size = fromIntegral . Set.size

instance Sized (HashMap k a) where
  size = fromIntegral . HashMap.size

instance Sized (HashSet a) where
  size = fromIntegral . HashSet.size

instance Sized (Seq a) where
  size = fromIntegral . Seq.length


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
  size = fromIntegral . theSize

instance Null a => Null (SizedThing a) where
  empty = SizedThing 0 empty
  null  = null . sizedThing

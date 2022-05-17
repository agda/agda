{-# LANGUAGE CPP #-}

-- | A thin, zero-cost wrapper over IntSet with types for elements
module Agda.Utils.IntSet.Typed where

import Control.DeepSeq

import Data.Data (Data)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Agda.Utils.Pretty (Pretty(..))
import Agda.Utils.Null (Null)
import Agda.Utils.Singleton (Singleton)
import qualified Agda.Utils.Singleton as Singleton

import GHC.Exts (IsList, Coercible, coerce)
import qualified GHC.Exts as Exts
#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup (Semigroup)
#endif

type IsInt a = Coercible a Int

newtype ISet a = ISet { runISet :: IntSet }
  deriving (Data, Eq, Ord, Semigroup, Monoid, Null, NFData)

instance IsInt a => Singleton a (ISet a) where
  singleton = coerce IntSet.singleton

instance IsInt a => IsList (ISet a) where
  type Item (ISet a) = a
  fromList = coerce IntSet.fromList
  toList   = coerce IntSet.toList

instance (Show a, IsInt a) => Show (ISet a) where show n = show (toList n)
instance (Pretty a, IsInt a) => Pretty (ISet a) where pretty n = pretty (toList n)

empty :: IsInt a => ISet a
empty = coerce IntSet.empty

fromList :: IsInt a => [a] -> ISet a
fromList = coerce IntSet.fromList

toList :: IsInt a => ISet a -> [a]
toList = coerce IntSet.toList

toAscList :: IsInt a => ISet a -> [a]
toAscList = coerce IntSet.toAscList

union :: IsInt a => ISet a -> ISet a -> ISet a
union = coerce IntSet.union

singleton :: IsInt a => a -> ISet a
singleton = coerce IntSet.singleton

member :: IsInt a => a -> ISet a -> Bool
member = coerce IntSet.member

null :: IsInt a => ISet a -> Bool
null = coerce IntSet.null

disjoint :: IsInt a => ISet a -> ISet a -> Bool
disjoint = coerce IntSet.disjoint

intersection :: IsInt a => ISet a -> ISet a -> ISet a
intersection = coerce IntSet.intersection

#if __GLASGOW_HASKELL__ >= 806
unions :: forall a f.
  (IsInt a, Foldable f, Coercible (f IntSet) (f (ISet a))) => f (ISet a) -> ISet a
unions = coerce @(f IntSet -> IntSet) IntSet.unions
#else
unions :: (IsInt a, Coercible [IntSet] [ISet a]) => [ISet a] -> ISet a
unions = coerce @([IntSet] -> IntSet) IntSet.unions
#endif

size :: IsInt a => ISet a -> Int
size = coerce IntSet.size

insert :: IsInt a => a -> ISet a -> ISet a
insert = coerce IntSet.insert

foldr :: forall a b. IsInt a => (a -> b -> b) -> b -> ISet a -> b
foldr f b a = coerce $ IntSet.foldr (coerce f) b (coerce a)

-- | A thin, zero-cost wrapper over IntSet with types for elements
module Agda.Utils.IntSet.Typed where

import Data.Data (Data)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Agda.Utils.Pretty (Pretty(..))
import Agda.Utils.Null (Null)

import GHC.Exts (IsList, Coercible, coerce)
import qualified GHC.Exts as Exts

type IsInt a = Coercible a Int

newtype ISet a = ISet { runISet :: IntSet }
  deriving (Data, Eq, Ord, Semigroup, Monoid, Null)

instance IsInt a => IsList (ISet a) where
  type Item (ISet a) = a
  fromList = coerce IntSet.fromList
  toList   = coerce IntSet.toList

instance (Show a, IsInt a) => Show (ISet a) where show n = show (toList n)
instance (Pretty a, IsInt a) => Pretty (ISet a) where pretty n = pretty (toList n)

empty :: IsInt a => ISet a
empty = coerce IntSet.empty

toList :: IsInt a => ISet a -> [a]
toList = coerce IntSet.toList

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

unions :: forall a f.
  (IsInt a, Foldable f, Coercible (f IntSet) (f (ISet a))) => f (ISet a) -> ISet a
unions = coerce @(f IntSet -> IntSet) IntSet.unions

size :: IsInt a => ISet a -> Int
size = coerce IntSet.size

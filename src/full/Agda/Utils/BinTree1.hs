-- | Binary trees, used for O(1) append.

module Agda.Utils.BinTree1 (BinTree1, prependToList, toList, toList1) where

import Agda.Utils.List1 (List1)
import Agda.Utils.List1 qualified as List1
import Agda.Utils.Singleton

import Agda.Utils.Impossible

data BinTree1 a
  = Lf1 a
  | !(BinTree1 a) :++: !(BinTree1 a)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Semigroup (BinTree1 a) where
  (<>) = (:++:)

instance Singleton a (BinTree1 a) where
  singleton = Lf1

prependToList :: BinTree1 a -> [a] -> [a]
prependToList = \case
  Lf1 a      -> (a:)
  t1 :++: t2 -> prependToList t1 . prependToList t2

toList :: BinTree1 a -> [a]
toList = (`prependToList` [])

toList1 :: BinTree1 a -> List1 a
toList1 = List1.fromListSafe __IMPOSSIBLE__ . toList

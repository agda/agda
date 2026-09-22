-- | Binary trees, used for O(1) append.

module Agda.Utils.BinTree (BinTree, prependToList, toList) where

import Agda.Utils.BinTree1 (BinTree1)
import Agda.Utils.BinTree1 qualified as BinTree1
import Agda.Utils.Null
import Agda.Utils.Singleton

import Agda.Utils.Impossible

data BinTree a
  = BT0
  | BT1 !(BinTree1 a)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Null (BinTree a) where
  empty = BT0
  null = \case
    BT0   -> True
    BT1 _ -> False

instance Semigroup (BinTree a) where
  BT0 <> t = t
  t <> BT0 = t
  BT1 t1 <> BT1 t2 = BT1 (t1 <> t2)

instance Monoid (BinTree a) where
  mempty = empty

instance Singleton a (BinTree a) where
  singleton = BT1 . singleton

prependToList :: BinTree a -> [a] -> [a]
prependToList = \case
  BT0   -> id
  BT1 t -> BinTree1.prependToList t

toList :: BinTree a -> [a]
toList = (`prependToList` [])

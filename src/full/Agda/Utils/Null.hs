{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE CPP               #-}

-- | Overloaded @null@ and @empty@ for collections and sequences.

module Agda.Utils.Null where

import Prelude hiding (null)

import Control.Monad

import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as ByteString
import Data.Function
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set

import Text.PrettyPrint (Doc, render)

import Agda.Utils.Bag (Bag)
import qualified Agda.Utils.Bag as Bag

class Null a where
  empty :: a
  null  :: a -> Bool
  -- ^ Satisfying @null empty == True@.

  default null :: Eq a => a -> Bool
  null = (== empty)

instance Null () where
  empty  = ()
  null _ = True

instance (Null a, Null b) => Null (a,b) where
  empty      = (empty, empty)
  null (a,b) = null a && null b

instance Null ByteString where
  empty = ByteString.empty
  null  = ByteString.null

instance Null [a] where
  empty = []
  null  = List.null

instance Null (Bag a) where
  empty = Bag.empty
  null  = Bag.null

instance Null (IntMap a) where
  empty = IntMap.empty
  null  = IntMap.null

instance Null IntSet where
  empty = IntSet.empty
  null  = IntSet.null

instance Null (Map k a) where
  empty = Map.empty
  null  = Map.null

instance Null (HashMap k a) where
  empty = HashMap.empty
  null  = HashMap.null

instance Null (HashSet a) where
  empty = HashSet.empty
  null  = HashSet.null

instance Null (Seq a) where
  empty = Seq.empty
  null  = Seq.null

instance Null (Set a) where
  empty = Set.empty
  null  = Set.null

-- | A 'Maybe' is 'null' when it corresponds to the empty list.
instance Null (Maybe a) where
  empty = Nothing
  null Nothing  = True
  null (Just a) = False

instance Null Doc where
  empty = mempty
  null  = (== mempty)

-- * Testing for null.

ifNull :: (Null a) => a -> b -> (a -> b) -> b
ifNull a b k = if null a then b else k a

ifNullM :: (Monad m, Null a) => m a -> m b -> (a -> m b) -> m b
ifNullM ma mb k = ma >>= \ a -> ifNull a mb k

whenNull :: (Monad m, Null a) => a -> m () -> m ()
whenNull = when . null

unlessNull :: (Monad m, Null a) => a -> (a -> m ()) -> m ()
unlessNull a k = unless (null a) $ k a

whenNullM :: (Monad m, Null a) => m a -> m () -> m ()
whenNullM ma k = ma >>= (`whenNull` k)

unlessNullM :: (Monad m, Null a) => m a -> (a -> m ()) -> m ()
unlessNullM ma k = ma >>= (`unlessNull` k)

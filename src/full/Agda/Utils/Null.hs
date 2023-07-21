{-# OPTIONS_GHC -Wunused-imports #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Overloaded @null@ and @empty@ for collections and sequences.

module Agda.Utils.Null where

import Prelude hiding (null)

import Control.Monad          ( when, unless )
import Control.Monad.Except   ( ExceptT )
import Control.Monad.Identity ( Identity(..) )
import Control.Monad.Reader   ( ReaderT )
import Control.Monad.State    ( StateT  )
import Control.Monad.Writer   ( WriterT )
import Control.Monad.Trans    ( lift    )

import Data.Maybe             ( isNothing )

import qualified Data.ByteString.Char8 as ByteStringChar8
import qualified Data.ByteString.Lazy as ByteStringLazy

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
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Text (Text)
import qualified Data.Text as Text

import Text.PrettyPrint (Doc, isEmpty)

import Agda.Utils.Bag (Bag)
import qualified Agda.Utils.Bag as Bag

import Agda.Utils.Impossible

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

instance (Null a, Null b, Null c) => Null (a,b,c) where
  empty        = (empty, empty, empty)
  null (a,b,c) = null a && null b && null c

instance (Null a, Null b, Null c, Null d) => Null (a,b,c,d) where
  empty          = (empty, empty, empty, empty)
  null (a,b,c,d) = null a && null b && null c && null d

instance Null ByteStringChar8.ByteString where
  empty = ByteStringChar8.empty
  null  = ByteStringChar8.null

instance Null ByteStringLazy.ByteString where
  empty = ByteStringLazy.empty
  null  = ByteStringLazy.null

instance Null Text where
  empty = Text.empty
  null  = Text.null

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
  null  = isNothing

-- | Viewing 'Bool' as @'Maybe' ()@, a boolean is 'null' when it is false.
instance Null Bool where
  empty = False
  null  = not

instance Null Doc where
  empty = mempty
  null  = isEmpty

instance Null a => Null (Identity a) where
  empty = return empty
  null  = null . runIdentity

instance Null a => Null (IO a) where
  empty = return empty
  null  = __IMPOSSIBLE__

instance (Null (m a), Monad m) => Null (ExceptT e m a) where
  empty = lift empty
  null  = __IMPOSSIBLE__

instance (Null (m a), Monad m) => Null (ReaderT r m a) where
  empty = lift empty
  null  = __IMPOSSIBLE__

instance (Null (m a), Monad m) => Null (StateT s m a) where
  empty = lift empty
  null  = __IMPOSSIBLE__

instance (Null (m a), Monad m, Monoid w) => Null (WriterT w m a) where
  empty = lift empty
  null  = __IMPOSSIBLE__

-- * Testing for null.

ifNull :: (Null a) => a -> b -> (a -> b) -> b
ifNull a b k = if null a then b else k a

ifNotNull :: (Null a) => a -> (a -> b) -> b -> b
ifNotNull a k b = ifNull a b k

ifNullM :: (Monad m, Null a) => m a -> m b -> (a -> m b) -> m b
ifNullM ma mb k = ma >>= \ a -> ifNull a mb k

ifNotNullM :: (Monad m, Null a) => m a -> (a -> m b) -> m b -> m b
ifNotNullM ma k mb = ifNullM ma mb k

whenNull :: (Monad m, Null a) => a -> m () -> m ()
whenNull = when . null

unlessNull :: (Monad m, Null a) => a -> (a -> m ()) -> m ()
unlessNull a k = unless (null a) $ k a

whenNullM :: (Monad m, Null a) => m a -> m () -> m ()
whenNullM ma k = ma >>= (`whenNull` k)

unlessNullM :: (Monad m, Null a) => m a -> (a -> m ()) -> m ()
unlessNullM ma k = ma >>= (`unlessNull` k)

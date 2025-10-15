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
import Control.Monad.Trans.Maybe

import Data.Maybe             ( isNothing )

import qualified Data.ByteString.Char8 as ByteStringChar8
import qualified Data.ByteString.Lazy as ByteStringLazy

import Data.EnumMap (EnumMap)
import qualified Data.EnumMap as EnumMap
import Data.EnumSet (EnumSet)
import qualified Data.EnumSet as EnumSet
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

import Text.PrettyPrint.Annotated (Doc, isEmpty)

import Agda.Utils.Bag (Bag)
import qualified Agda.Utils.Bag as Bag
import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as VarSet

import Agda.Utils.Unsafe (unsafeComparePointers)
import Agda.Utils.Impossible

class Null a where
  empty :: a
  null  :: a -> Bool
  -- ^ Satisfying @null empty == True@.

  -- | The default implementation of 'null' compares with 'empty',
  --   first trying pointer equality, then falling back to 'Eq' equality.
  default null :: Eq a => a -> Bool
  null a = unsafeComparePointers a empty || a == empty

instance Null () where
  empty  = ()
  {-# INLINE empty #-}
  null _ = True
  {-# INLINE null #-}

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
  {-# INLINE empty #-}
  null  = ByteStringChar8.null
  {-# INLINE null #-}

instance Null ByteStringLazy.ByteString where
  empty = ByteStringLazy.empty
  {-# INLINE empty #-}
  null  = ByteStringLazy.null
  {-# INLINE null #-}

instance Null Text where
  empty = Text.empty
  {-# INLINE empty #-}
  null  = Text.null
  {-# INLINE null #-}

instance Null [a] where
  empty = []
  {-# INLINE empty #-}
  null  = List.null
  {-# INLINE null #-}

instance Null (Bag a) where
  empty = Bag.empty
  {-# INLINE empty #-}
  null  = Bag.null
  {-# INLINE null #-}

instance Null (EnumMap k a) where
  empty = EnumMap.empty
  {-# INLINE empty #-}
  null  = EnumMap.null
  {-# INLINE null #-}

instance Null (EnumSet a) where
  empty = EnumSet.empty
  {-# INLINE empty #-}
  null  = EnumSet.null
  {-# INLINE null #-}

instance Null (IntMap a) where
  empty = IntMap.empty
  {-# INLINE empty #-}
  null  = IntMap.null
  {-# INLINE null #-}

instance Null IntSet where
  empty = IntSet.empty
  {-# INLINE empty #-}
  null  = IntSet.null
  {-# INLINE null #-}

instance Null (Map k a) where
  empty = Map.empty
  {-# INLINE empty #-}
  null  = Map.null
  {-# INLINE null #-}

instance Null (HashMap k a) where
  empty = HashMap.empty
  {-# INLINE empty #-}
  null  = HashMap.null
  {-# INLINE null #-}

instance Null (HashSet a) where
  empty = HashSet.empty
  {-# INLINE empty #-}
  null  = HashSet.null
  {-# INLINE null #-}

instance Null (Seq a) where
  empty = Seq.empty
  {-# INLINE empty #-}
  null  = Seq.null
  {-# INLINE null #-}

instance Null (Set a) where
  empty = Set.empty
  {-# INLINE empty #-}
  null  = Set.null
  {-# INLINE null #-}

instance Null VarSet where
  empty = VarSet.empty
  {-# INLINE empty #-}
  null = VarSet.null
  {-# INLINE null #-}

-- | A 'Maybe' is 'null' when it corresponds to the empty list.
instance Null (Maybe a) where
  empty = Nothing
  {-# INLINE empty #-}
  null  = isNothing
  {-# INLINE null #-}

-- | Viewing 'Bool' as @'Maybe' ()@, a boolean is 'null' when it is false.
instance Null Bool where
  empty = False
  {-# INLINE empty #-}
  null  = not
  {-# INLINE null #-}

instance Null (Doc a) where
  empty = mempty
  null  = isEmpty

instance Null a => Null (Identity a) where
  empty = return empty
  {-# INLINE empty #-}
  null  = null . runIdentity
  {-# INLINE null #-}

instance Null a => Null (IO a) where
  empty = return empty
  {-# INLINE empty #-}
  null  = __IMPOSSIBLE__
  {-# NOINLINE null #-}

instance (Null (m a), Monad m) => Null (ExceptT e m a) where
  empty = lift empty
  {-# INLINE empty #-}
  null  = __IMPOSSIBLE__
  {-# NOINLINE null #-}

instance (Null (m a), Monad m) => Null (MaybeT m a) where
  empty = lift empty
  {-# INLINE empty #-}
  null  = __IMPOSSIBLE__
  {-# NOINLINE null #-}

instance (Null (m a), Monad m) => Null (ReaderT r m a) where
  empty = lift empty
  {-# INLINE empty #-}
  null  = __IMPOSSIBLE__
  {-# NOINLINE null #-}

instance (Null (m a), Monad m) => Null (StateT s m a) where
  empty = lift empty
  {-# INLINE empty #-}
  null  = __IMPOSSIBLE__
  {-# NOINLINE null #-}

instance (Null (m a), Monad m, Monoid w) => Null (WriterT w m a) where
  empty = lift empty
  {-# INLINE empty #-}
  null  = __IMPOSSIBLE__
  {-# NOINLINE null #-}

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

applyUnlessNull :: (Null a) => a -> (a -> b -> b) -> (b -> b)
applyUnlessNull a f = if null a then id else f a

-- | Disjunction (interpreting @null _@ as @False@).
catchNull :: Null a => a -> a -> a
catchNull a b = if null a then b else a

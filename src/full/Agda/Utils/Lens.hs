{-# OPTIONS_GHC -Wunused-imports #-}

-- | A cut-down implementation of lenses, with names taken from
--   Edward Kmett's lens package.

module Agda.Utils.Lens
  ( module Agda.Utils.Lens
  , (<&>) -- reexported from Agda.Utils.Functor
  ) where

import Control.Applicative ( Const(Const), getConst )
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Functor.Identity

import Agda.Utils.Functor ((<&>))

-- * Type-preserving lenses.

-- | Van Laarhoven style homogeneous lenses.
--   Mnemoic: "Lens outer inner", same type argument order as 'get :: o -> i'.
type Lens' o i = forall f. Functor f => (i -> f i) -> o -> f o

type LensGet o i = o -> i
type LensSet o i = i -> o -> o
type LensMap o i = (i -> i) -> o -> o

-- * Some simple lenses.

lFst :: Lens' (a, b) a
lFst f (x, y) = (, y) <$> f x

lSnd :: Lens' (a, b) b
lSnd f (x, y) = (x,) <$> f y

-- * Elementary lens operations.

infixl 8 ^.
-- | Get inner part @i@ of structure @o@ as designated by @Lens' o i@.
(^.) :: o -> Lens' o i -> i
o ^. l = getConst $ l Const o

-- | Set inner part @i@ of structure @o@ as designated by @Lens' o i@.
set :: Lens' o i -> LensSet o i
set l = over l . const

-- | Modify inner part @i@ of structure @o@ using a function @i -> i@.
over :: Lens' o i -> LensMap o i
over l f o = runIdentity $ l (Identity . f) o


-- * State accessors and modifiers using 'StateT'.

-- | Focus on a part of the state for a stateful computation.
focus :: Monad m => Lens' o i -> StateT i m a -> StateT o m a
focus l m = StateT $ \ o -> do
  (a, i) <- runStateT m (o ^. l)
  return (a, set l i o)

-- * State accessors and modifiers using 'MonadState'.

-- | Read a part of the state.
use :: MonadState o m => Lens' o i -> m i
use l = do !x <- gets (^. l)
           return x

infix 4 .=
-- | Write a part of the state.
(.=) :: MonadState o m => Lens' o i -> i -> m ()
l .= i = modify $ set l i

infix 4 %=
-- | Modify a part of the state.
(%=) :: MonadState o m => Lens' o i -> (i -> i) -> m ()
l %= f = modify $ over l f

infix 4 %==
-- | Modify a part of the state monadically.
(%==) :: MonadState o m => Lens' o i -> (i -> m i) -> m ()
l %== f = put =<< l f =<< get

infix 4 %%=
-- | Modify a part of the state monadically, and return some result.
(%%=) :: MonadState o m => Lens' o i -> (i -> m (i, r)) -> m r
l %%= f = do
  o <- get
  (o', r) <- runWriterT $ l (WriterT . f) o
  put o'
  return r

-- | Modify a part of the state locally.
locallyState :: MonadState o m => Lens' o i -> (i -> i) -> m r -> m r
locallyState l f k = do
  old <- use l
  l %= f
  x <- k
  l .= old
  return x

-- * Read-only state accessors and modifiers.

-- | Ask for part of read-only state.
view :: MonadReader o m => Lens' o i -> m i
view l = asks (^. l)

-- | Modify a part of the state in a subcomputation.
locally :: MonadReader o m => Lens' o i -> (i -> i) -> m a -> m a
locally l = local . over l

locally' :: ((o -> o) -> m a -> m a) -> Lens' o i -> (i -> i) -> m a -> m a
locally' local l = local . over l

-- * Lenses for collections

-- | Access a map value at a given key.
key :: Ord k => k -> Lens' (Map k v) (Maybe v)
key k f m = f (Map.lookup k m) <&> \ v -> Map.alter (const v) k m

-- | Focus on given element in a set.
contains :: Ord k => k -> Lens' (Set k) Bool
contains k f s = f (Set.member k s) <&> \case
  True  -> Set.insert k s
  False -> Set.delete k s

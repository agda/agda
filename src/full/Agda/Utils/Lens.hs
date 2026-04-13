{-# OPTIONS_GHC -Wunused-imports #-}

-- | A cut-down implementation of lenses, with names mostly taken from
--   Edward Kmett's lens package.

module Agda.Utils.Lens
  ( module Agda.Utils.Lens
  , (<&>) -- reexported from Agda.Utils.Functor
  , (&&&) -- reexported from Control.Arrow
  , (&)   -- reexported from Data.Function
  ) where

import Control.Applicative ( Const(Const), getConst )
import Control.Arrow       ( (&&&) )
import Control.Monad.State.Class (MonadState(..), gets, modify, modify')
import Control.Monad.Reader.Class (MonadReader(..))

import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Functor.Identity
import Data.Function ((&))
import Data.Functor ((<&>))

--------------------------------------------------------------------------------

-- | Van Laarhoven style homogeneous lenses.
--   Mnemoic: "Lens outer inner", same type argument order as 'get :: o -> i'.
type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t
type Lens' s a = Lens s s a a

type LensGet o i = o -> i
type LensSet o i = i -> o -> o
type LensMap o i = (i -> i) -> o -> o

type Getting r s a   = (a -> Const r a) -> s -> Const r s
type ASetter s t a b = (a -> Identity b) -> s -> Identity t

-- * Elementary lens operations.

infixl 8 ^.
{-# INLINE (^.) #-}
-- | Get inner part @i@ of structure @o@ as designated by @Lens' o i@.
(^.) :: s -> Getting a s a -> a
s ^. l = getConst (l Const s)

{-# INLINE set #-}
-- | Set inner part @i@ of structure @o@ as designated by @Lens' o i@.
set :: ASetter s t a b -> b -> s -> t
set l = \b -> over l (\_ -> b)

{-# INLINE set' #-}
-- | Strictly set inner part @i@ of structure @o@ as designated by @Lens' o i@.
set' :: ASetter s t a b -> b -> s -> t
set' l = \ !b -> over l (\_ -> b)

{-# INLINE (.~) #-}
infixr 4 .~
(.~) :: ASetter s t a b -> b -> s -> t
(.~) = set

{-# INLINE over #-}
-- | Modify inner part @i@ of structure @o@ using a function @i -> i@.
over :: ASetter s t a b -> (a -> b) -> s -> t
over l = \f s -> runIdentity (l (Identity . f) s)

{-# INLINE over' #-}
-- | Strictly modify inner part @i@ of structure @o@ using a function @i -> i@.
over' :: ASetter s t a b -> (a -> b) -> s -> t
over' l = \f s -> runIdentity (l (\x -> Identity $! f x) s)

infixr 4 %~
(%~) :: ASetter s t a b -> (a -> b) -> s -> t
(%~) = over

infixr 4 %~!
(%~!) :: ASetter s t a b -> (a -> b) -> s -> t
(%~!) = over'

{-# INLINE iso #-}
-- | Build a lens out of an isomorphism.
iso :: (o -> i) -> (i -> o) -> Lens' o i
iso get set = \f -> fmap set . f . get

{-# INLINE lens #-}
-- | Build a lens from a getter and a setter.
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens sa sbt = \afb s -> sbt s <$> afb (sa s)

{-# INLINE lensProduct #-}
-- | Only sound if the lenses are disjoint!
lensProduct :: Lens' s a -> Lens' s b -> Lens' s (a , b)
lensProduct l1 l2 = lens (\s -> (s ^. l1, s ^. l2)) (\s (a, b) -> set l1 a $ set l2 b s)

-- * Reader/State accessors and modifiers.

-- | Read part of the environment.
{-# INLINE view #-}
view :: MonadReader s m => Getting a s a -> m a
view l = (^. l) <$> ask

{-# INLINE use #-}
-- | Read a part of the state.
use :: MonadState s m => Getting a s a -> m a
use l = gets (^. l)

{-# INLINE (.=) #-}
infix 4 .=
-- | Write a part of the state.
(.=) :: MonadState s m => ASetter s s a b -> b -> m ()
l .= b = modify (set l b)

{-# INLINE (.=!) #-}
infix 4 .=!
-- | Strictly write a part of the state.
(.=!) :: MonadState s m => ASetter s s a b -> b -> m ()
l .=! b = modify' (set l b)

{-# INLINE (%=) #-}
infix 4 %=
-- | Modify a part of the state.
(%=) :: MonadState s m => ASetter s s a b -> (a -> b) -> m ()
l %= f = modify (over l f)

{-# INLINE (%=!) #-}
infix 4 %=!
-- | Strictly modify a part of the state.
(%=!) :: MonadState s m => ASetter s s a b -> (a -> b) -> m ()
l %=! f = modify' (over l f)

{-# INLINE (%==) #-}
infix 4 %==
-- | Modify a part of the state monadically.
(%==) :: MonadState s m => Lens' s a -> (a -> m a) -> m ()
l %== f = do
  a <- use l
  a <- f a
  modify (set l a)

{-# INLINE (%==!) #-}
infix 4 %==!
-- | Strictly modify a part of the state monadically.
(%==!) :: MonadState s m => Lens' s a -> (a -> m a) -> m ()
l %==! f = do
  a <- use l
  a <- f a
  modify' (set l a)

{-# INLINE (%%=) #-}
infix 4 %%=
-- | Modify a part of the state monadically, and return some result.
(%%=) :: MonadState o m => Lens' o i -> (i -> m (i, r)) -> m r
l %%= f = do
  i <- use l
  (i', r) <- f i
  l .= i'
  return r

{-# INLINE (%%=!) #-}
infix 4 %%=!
-- | Strictly modify a part of the state monadically, and return some result.
(%%=!) :: MonadState o m => Lens' o i -> (i -> m (i, r)) -> m r
l %%=! f = do
  i <- use l
  (!i', !r) <- f i
  l .= i'
  return r

{-# INLINE locallyState #-}
-- | Modify a part of the state locally.
locallyState :: MonadState o m => Lens' o i -> (i -> i) -> m r -> m r
locallyState l f k = do
  old <- use l
  l %= f
  x <- k
  l .= old
  return x

{-# INLINE locally #-}
-- | Modify a part of the state in a subcomputation.
locally :: MonadReader r m => ASetter r r a b -> (a -> b) -> m c -> m c
locally l = local . over l

-- * Lenses for collections

{-# INLINE key #-}
-- | Access a map value at a given key.
key :: Ord k => k -> Lens' (Map k v) (Maybe v)
key k = \f s -> Map.alterF f k s

{-# INLINE contains #-}
-- | Focus on given element in a set.
contains :: Ord k => k -> Lens' (Set k) Bool
contains k f s = f (Set.member k s) <&> \case
  True  -> Set.insert k s
  False -> Set.delete k s

-- Tuple field lenses (up to 5-tuples currently)
--------------------------------------------------------------------------------

class Field1 s t a b | s -> a, t -> b, s b -> t, t a -> s where
  _1  :: Lens s t a b
  _1' :: Lens s t a b

instance Field1 (a,b) (a',b) a a' where
  _1  = \k (a,b) -> (\  a -> (a,b)) <$> k a
  _1' = \k (a,b) -> (\ !a -> (a,b)) <$> k a
  {-# INLINE _1 #-}
  {-# INLINE _1' #-}

instance Field1 (a,b,c) (a',b,c) a a' where
  _1  = \k (a,b,c) -> (\  a -> (a,b,c)) <$> k a
  _1' = \k (a,b,c) -> (\ !a -> (a,b,c)) <$> k a
  {-# INLINE _1 #-}
  {-# INLINE _1' #-}

instance Field1 (a,b,c,d) (a',b,c,d) a a' where
  _1  = \k (a,b,c,d) -> (\  a -> (a,b,c,d)) <$> k a
  _1' = \k (a,b,c,d) -> (\ !a -> (a,b,c,d)) <$> k a
  {-# INLINE _1 #-}
  {-# INLINE _1' #-}

instance Field1 (a,b,c,d,e) (a',b,c,d,e) a a' where
  _1  = \k (a,b,c,d,e) -> (\  a -> (a,b,c,d,e)) <$> k a
  _1' = \k (a,b,c,d,e) -> (\ !a -> (a,b,c,d,e)) <$> k a
  {-# INLINE _1 #-}
  {-# INLINE _1' #-}

class Field2 s t a b | s -> a, t -> b, s b -> t, t a -> s where
  _2  :: Lens s t a b
  _2' :: Lens s t a b

instance Field2 (a,b) (a,b') b b' where
  _2  = \k (a,b) -> (\  b -> (a,b)) <$> k b
  _2' = \k (a,b) -> (\ !b -> (a,b)) <$> k b
  {-# INLINE _2 #-}
  {-# INLINE _2' #-}

instance Field2 (a,b,c) (a,b',c) b b' where
  _2  = \k (a,b,c) -> (\  b -> (a,b,c)) <$> k b
  _2' = \k (a,b,c) -> (\ !b -> (a,b,c)) <$> k b
  {-# INLINE _2 #-}
  {-# INLINE _2' #-}

instance Field2 (a,b,c,d) (a,b',c,d) b b' where
  _2  = \k (a,b,c,d) -> (\  b -> (a,b,c,d)) <$> k b
  _2' = \k (a,b,c,d) -> (\ !b -> (a,b,c,d)) <$> k b
  {-# INLINE _2 #-}
  {-# INLINE _2' #-}

instance Field2 (a,b,c,d,e) (a,b',c,d,e) b b' where
  _2  = \k (a,b,c,d,e) -> (\  b -> (a,b,c,d,e)) <$> k b
  _2' = \k (a,b,c,d,e) -> (\ !b -> (a,b,c,d,e)) <$> k b
  {-# INLINE _2 #-}
  {-# INLINE _2' #-}

class Field3 s t a b | s -> a, t -> b, s b -> t, t a -> s where
  _3  :: Lens s t a b
  _3' :: Lens s t a b

instance Field3 (a,b,c) (a,b,c') c c' where
  _3  = \k (a,b,c) -> (\  c -> (a,b,c)) <$> k c
  _3' = \k (a,b,c) -> (\ !c -> (a,b,c)) <$> k c
  {-# INLINE _3 #-}
  {-# INLINE _3' #-}

instance Field3 (a,b,c,d) (a,b,c',d) c c' where
  _3  = \k (a,b,c,d) -> (\  c -> (a,b,c,d)) <$> k c
  _3' = \k (a,b,c,d) -> (\ !c -> (a,b,c,d)) <$> k c
  {-# INLINE _3 #-}
  {-# INLINE _3' #-}

instance Field3 (a,b,c,d,e) (a,b,c',d,e) c c' where
  _3  = \k (a,b,c,d,e) -> (\  c -> (a,b,c,d,e)) <$> k c
  _3' = \k (a,b,c,d,e) -> (\ !c -> (a,b,c,d,e)) <$> k c
  {-# INLINE _3 #-}
  {-# INLINE _3' #-}

class Field4 s t a b | s -> a, t -> b, s b -> t, t a -> s where
  _4  :: Lens s t a b
  _4' :: Lens s t a b

instance Field4 (a,b,c,d) (a,b,c,d') d d' where
  _4  = \k (a,b,c,d) -> (\  d -> (a,b,c,d)) <$> k d
  _4' = \k (a,b,c,d) -> (\ !d -> (a,b,c,d)) <$> k d
  {-# INLINE _4 #-}
  {-# INLINE _4' #-}

instance Field4 (a,b,c,d,e) (a,b,c,d',e) d d' where
  _4  = \k (a,b,c,d,e) -> (\  d -> (a,b,c,d,e)) <$> k d
  _4' = \k (a,b,c,d,e) -> (\ !d -> (a,b,c,d,e)) <$> k d
  {-# INLINE _4 #-}
  {-# INLINE _4' #-}

class Field5 s t a b | s -> a, t -> b, s b -> t, t a -> s where
  _5  :: Lens s t a b
  _5' :: Lens s t a b

instance Field5 (a,b,c,d,e) (a,b,c,d,e') e e' where
  _5  = \k (a,b,c,d,e) -> (\  e -> (a,b,c,d,e)) <$> k e
  _5' = \k (a,b,c,d,e) -> (\ !e -> (a,b,c,d,e)) <$> k e
  {-# INLINE _5 #-}
  {-# INLINE _5' #-}

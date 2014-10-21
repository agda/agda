{-# OPTIONS_GHC -fwarn-missing-signatures #-}

{-# LANGUAGE RankNTypes #-}

-- | A cut-down implementation of lenses, with names taken from
--   Edward Kmett's lens package.

module Agda.Utils.Lens
  ( module Agda.Utils.Lens
  , (<&>) -- reexported from Agda.Utils.Functor
  ) where

import Control.Monad.State
import Control.Monad.Reader

import Data.Functor.Constant
import Data.Functor.Identity

import Agda.Utils.Functor ((<&>))

-- * Type-preserving lenses.

-- | Van Laarhoven style homogeneous lenses.
--   Mnemoic: "Lens inner outer".
type Lens' i o = forall f. Functor f => (i -> f i) -> o -> f o


-- * Elementary lens operations.

infixl 8 ^.
-- | Get inner part @i@ of structure @o@ as designated by @Lens' i o@.
(^.) :: o -> Lens' i o -> i
o ^. l = getConstant $ l Constant o

-- | Set inner part @i@ of structure @o@ as designated by @Lens' i o@.
set :: Lens' i o -> i -> o -> o
set l = over l . const

-- | Modify inner part @i@ of structure @o@ using a function @i -> i@.
over :: Lens' i o -> (i -> i) -> o -> o
over l f o = runIdentity $ l (Identity . f) o


-- * State accessors and modifiers.

-- | Read a part of the state.
use :: MonadState o m => Lens' i o -> m i
use l = gets (^. l)

infix  4 .=
-- | Write a part of the state.
(.=) :: MonadState o m => Lens' i o -> i -> m ()
l .= i = modify $ set l i

infix  4 %=
-- | Modify a part of the state.
(%=) :: MonadState o m => Lens' i o -> (i -> i) -> m ()
l %= f = modify $ over l f


-- * Read-only state accessors and modifiers.

-- | Ask for part of read-only state.
view :: MonadReader o m => Lens' i o -> m i
view l = asks (^. l)

-- | Modify a part of the state in a subcomputation.
locally :: MonadReader o m => Lens' i o -> (i -> i) -> m a -> m a
locally l = local . over l


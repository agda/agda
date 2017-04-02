{-# LANGUAGE CPP #-}

-- | Utilities for functors.

module Agda.Utils.Functor
  ( module Agda.Utils.Functor
  , (<$>) -- from Data.Functor
  )
  where

import Control.Applicative ( Const(Const), getConst )

import Data.Functor
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Functor.Classes

infixr 4 $>

($>) :: Functor f => f a -> b -> f b
($>) = flip (<$)

infixr 9 <.>

-- | Composition: pure function after functorial (monadic) function.
(<.>) :: Functor m => (b -> c) -> (a -> m b) -> a -> m c
(f <.> g) a = f <$> g a

-- | The true pure @for@ loop.
--   'Data.Traversable.for' is a misnomer, it should be @forA@.
for :: Functor m => m a -> (a -> b) -> m b
for = flip fmap

infix 4 <&>

-- | Infix version of 'for'.
(<&>) :: Functor m => m a -> (a -> b) -> m b
(<&>) = for

-- | A decoration is a functor that is traversable into any functor.
--
--   The 'Functor' superclass is given because of the limitations
--   of the Haskell class system.
--   @traverseF@ actually implies functoriality.
--
--   Minimal complete definition: @traverseF@ or @distributeF@.
class Functor t => Decoration t where

  -- | @traverseF@ is the defining property.
  traverseF :: Functor m => (a -> m b) -> t a -> m (t b)
  traverseF f = distributeF . fmap f

  -- | Decorations commute into any functor.
  distributeF :: (Functor m) => t (m a) -> m (t a)
  distributeF = traverseF id

-- | Any decoration is traversable with @traverse = traverseF@.
--   Just like any 'Traversable' is a functor, so is
--   any decoration, given by just @traverseF@, a functor.
dmap :: Decoration t => (a -> b) -> t a -> t b
dmap f = runIdentity . traverseF (Identity . f)

-- | Any decoration is a lens.  @set@ is a special case of @dmap@.
dget :: Decoration t => t a -> a
dget = getConst . traverseF Const

-- | The identity functor is a decoration.
instance Decoration Identity where
  traverseF f (Identity x) = Identity <$> f x

-- | Decorations compose.  (Thus, they form a category.)
instance (Decoration d, Decoration t) => Decoration (Compose d t) where
  -- traverseF . traverseF :: Functor m => (a -> m b) -> d (t a) -> m (d (t a))
  traverseF f (Compose x) = Compose <$> traverseF (traverseF f) x

-- Not a decoration are:
--
-- * The constant functor.
-- * Maybe.  Can only be traversed into pointed functors.
-- * Other disjoint sum types, like lists etc.
--   (Can only be traversed into Applicative.)

-- | A typical decoration is pairing with some stuff.
instance Decoration ((,) a) where
  traverseF f (a, x) = (a,) <$> f x

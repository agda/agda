{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Agda.Utils.Update
  ( Change
  , MonadChange(..)
  , runChange
  , Updater
  , sharing
  , runUpdater
  , dirty
  , ifDirty
  , Updater1(..)
  , Updater2(..)
  ) where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Trans
import Control.Monad.Writer.Strict

import Data.Traversable (Traversable(..), traverse)

import Data.Monoid

import Agda.Utils.Tuple

-- * Change monad.

-- | The class of change monads.
class Monad m => MonadChange m where
  tellDirty   :: m () -- ^ Mark computation as having changed something.
  listenDirty :: m a -> m (a, Bool)

-- | The @ChangeT@ monad transformer.
newtype ChangeT m a = ChangeT { fromChangeT :: WriterT Any m a }
  deriving (Functor, Applicative, Monad, MonadTrans)

instance Monad m => MonadChange (ChangeT m) where
  tellDirty     = ChangeT $ tell $ Any True
  listenDirty m = ChangeT $ do
    (a, Any dirty) <- listen (fromChangeT m)
    return (a, dirty)

-- | A mock change monad.
instance MonadChange Identity where
  tellDirty                = Identity ()
  listenDirty (Identity a) = Identity (a, True)

-- * Pure endo function and updater

type EndoFun a = a -> a
type Updater a = a -> Change a

-- BEGIN REAL STUFF

-- | The @Change@ monad.
newtype Change a = Change { fromChange :: Writer Any a }
  deriving (Functor, Applicative, Monad)

instance MonadChange Change where
  tellDirty = Change $ tell $ Any True
  listenDirty m = Change $ do
    (a, Any dirty) <- listen (fromChange m)
    return (a, dirty)

-- | Run a 'Change' computation, returning result plus change flag.
runChange :: Change a -> (a, Bool)
runChange = mapSnd getAny . runWriter . fromChange

-- | Blindly run an updater.
runUpdater :: Updater a -> a -> (a, Bool)
runUpdater f a = runChange $ f a

-- | Mark a computation as dirty.
dirty :: Updater a
dirty a = do
  tellDirty
  return a

{-# SPECIALIZE ifDirty :: Change a -> (a -> Change b) -> (a -> Change b) -> Change b #-}
{-# SPECIALIZE ifDirty :: Identity a -> (a -> Identity b) -> (a -> Identity b) -> Identity b #-}
ifDirty :: MonadChange m => m a -> (a -> m b) -> (a -> m b) -> m b
ifDirty m f g = do
  (a, dirty) <- listenDirty m
  if dirty then f a else g a

-- * Proper updater (Q-combinators)

-- | Replace result of updating with original input if nothing has changed.
sharing :: Updater a -> Updater a
sharing f a = do
  (a', changed) <- listenDirty $ f a
  return $ if changed then a' else a

-- | Eval an updater (using 'sharing').
evalUpdater :: Updater a -> EndoFun a
evalUpdater f a = fst $ runWriter $ fromChange $ sharing f a

-- END REAL STUFF

-- * Updater transformer classes

-- ** Unary (functors)

-- | Like 'Functor', but preserving sharing.
class Traversable f => Updater1 f where
  updater1 :: Updater a -> Updater (f a)
  updates1 :: Updater a -> Updater (f a) -- ^ @= sharing . updater1@
  update1  :: Updater a -> EndoFun (f a)

  updater1   = traverse
  updates1 f = sharing $ updater1 f
  update1  f = evalUpdater $ updater1 f

instance Updater1 Maybe where

instance Updater1 [] where
  updater1 f []       = return []
  updater1 f (x : xs) = (:) <$> f x <*> updates1 f xs

-- ** Binary (bifunctors)

-- | Like 'Bifunctor', but preserving sharing.
class Updater2 f where
  updater2 :: Updater a -> Updater b -> Updater (f a b)
  updates2 :: Updater a -> Updater b -> Updater (f a b)
  update2  :: Updater a -> Updater b -> EndoFun (f a b)

  updates2 f1 f2 = sharing $ updater2 f1 f2
  update2  f1 f2 = evalUpdater $ updater2 f1 f2

instance Updater2 (,) where
  updater2 f1 f2 (a,b) = (,) <$> sharing f1 a <*> sharing f2 b

instance Updater2 Either where
  updater2 f1 f2 (Left a)  = Left <$> f1 a
  updater2 f1 f2 (Right b) = Right <$> f2 b


{-- BEGIN MOCK

-- * Mock updater

type Change = Identity

-- | Replace result of updating with original input if nothing has changed.
{-# INLINE sharing #-}
sharing :: Updater a -> Updater a
sharing f a = f a

-- | Run an updater.
{-# INLINE evalUpdater #-}
evalUpdater :: Updater a -> EndoFun a
evalUpdater f a = runIdentity (f a)

-- | Mark a computation as dirty.
{-# INLINE dirty #-}
dirty :: Updater a
dirty = Identity

{-# INLINE ifDirty #-}
ifDirty :: Identity a -> (a -> Identity b) -> (a -> Identity b) -> Identity b
ifDirty m f g = m >>= f

-- END MOCK -}

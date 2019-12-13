{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Agda.Utils.Update
  ( ChangeT
  , runChangeT, mapChangeT
  , UpdaterT
  , runUpdaterT
  , Change
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

import Control.Monad.Fail (MonadFail)
import Control.Monad.Identity
import Control.Monad.Trans
import Control.Monad.Trans.Identity
import Control.Monad.Writer.Strict

import Data.Traversable (Traversable(..), traverse)

import Agda.Utils.Tuple

-- * Change monad.

-- | The class of change monads.
class Monad m => MonadChange m where
  tellDirty   :: m () -- ^ Mark computation as having changed something.
  listenDirty :: m a -> m (a, Bool)

-- | The @ChangeT@ monad transformer.
newtype ChangeT m a = ChangeT { fromChangeT :: WriterT Any m a }
  deriving (Functor, Applicative, Monad, MonadTrans, MonadFail, MonadIO)

instance Monad m => MonadChange (ChangeT m) where
  tellDirty     = ChangeT $ tell $ Any True
  listenDirty m = ChangeT $ do
    (a, Any dirty) <- listen (fromChangeT m)
    return (a, dirty)

-- | Run a 'ChangeT' computation, returning result plus change flag.
runChangeT :: Functor m => ChangeT m a -> m (a, Bool)
runChangeT = fmap (mapSnd getAny) . runWriterT . fromChangeT

-- | Run a 'ChangeT' computation, but ignore change flag.
execChangeT :: Functor m => ChangeT m a -> m a
execChangeT = fmap fst . runChangeT

-- | Map a 'ChangeT' computation (monad transformer action).
mapChangeT :: (m (a, Any) -> n (b, Any)) -> ChangeT m a -> ChangeT n b
mapChangeT f (ChangeT m) = ChangeT (mapWriterT f m)

-- Don't actually track changes with the identity monad:

-- | A mock change monad.  Always assume change has happened.
instance MonadChange Identity where
  tellDirty   = return ()
  listenDirty = fmap (,True)

instance Monad m => MonadChange (IdentityT m) where
  tellDirty   = IdentityT    $ return ()
  listenDirty = mapIdentityT $ fmap (,True)

-- * Pure endo function and updater

type UpdaterT m a = a -> ChangeT m a

-- | Blindly run an updater.
runUpdaterT :: Functor m => UpdaterT m a -> a -> m (a, Bool)
runUpdaterT f a = runChangeT $ f a

type EndoFun a = a -> a
type Change  a = ChangeT Identity a
type Updater a = UpdaterT Identity a

fromChange :: Change a -> Writer Any a
fromChange = fromChangeT

-- | Run a 'Change' computation, returning result plus change flag.
{-# INLINE runChange #-}
runChange :: Change a -> (a, Bool)
runChange = runIdentity . runChangeT

-- | Blindly run an updater.
{-# INLINE runUpdater #-}
runUpdater :: Updater a -> a -> (a, Bool)
runUpdater f a = runChange $ f a

-- | Mark a computation as dirty.
dirty :: Monad m => UpdaterT m a
dirty a = do
  tellDirty
  return a

{-# SPECIALIZE ifDirty :: Change a -> (a -> Change b) -> (a -> Change b) -> Change b #-}
{-# SPECIALIZE ifDirty :: Identity a -> (a -> Identity b) -> (a -> Identity b) -> Identity b #-}
ifDirty :: (Monad m, MonadChange m) => m a -> (a -> m b) -> (a -> m b) -> m b
ifDirty m f g = do
  (a, dirty) <- listenDirty m
  if dirty then f a else g a

-- * Proper updater (Q-combinators)

-- | Replace result of updating with original input if nothing has changed.
sharing :: Monad m => UpdaterT m a -> UpdaterT m a
sharing f a = do
  (a', changed) <- listenDirty $ f a
  return $ if changed then a' else a

-- | Eval an updater (using 'sharing').
evalUpdater :: Updater a -> EndoFun a
evalUpdater f a = fst $ runChange $ sharing f a

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

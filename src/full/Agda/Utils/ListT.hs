{-# LANGUAGE UndecidableInstances  #-}  -- Due to limitations of funct.dep.
{-# LANGUAGE CPP  #-}

-- | @ListT@ done right,
--   see https://www.haskell.org/haskellwiki/ListT_done_right_alternative
--
--   There is also the @list-t@ package on hackage (Nikita Volkov)
--   but it again depends on other packages we do not use yet,
--   so we rather implement the few bits we need afresh.

module Agda.Utils.ListT where

import Control.Applicative ( Alternative((<|>), empty) )
import Control.Monad
import Control.Monad.Fail as Fail
import Control.Monad.Reader
import Control.Monad.State

#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup
#endif

import Agda.Utils.Maybe

-- | Lazy monadic computation of a list of results.
newtype ListT m a = ListT { runListT :: m (Maybe (a, ListT m a)) }
  deriving (Functor)

-- | Boilerplate function to lift 'MonadReader' through the 'ListT' transformer.
mapListT :: (m (Maybe (a, ListT m a)) -> n (Maybe (b, ListT n b))) -> ListT m a -> ListT n b
mapListT f = ListT . f . runListT

-- * List operations

-- | The empty lazy list.
nilListT :: Monad m => ListT m a
nilListT = ListT $ return Nothing

-- | Consing a value to a lazy list.
consListT :: Monad m => a -> ListT m a -> ListT m a
consListT a l = ListT $ return $ Just (a, l)

-- | Singleton lazy list.
sgListT ::  Monad m => a -> ListT m a
sgListT a = consListT a nilListT

-- | Case distinction over lazy list.
caseListT :: Monad m => ListT m a -> m b -> (a -> ListT m a -> m b) -> m b
caseListT l nil cons = caseMaybeM (runListT l) nil $ uncurry cons

-- | Folding a lazy list, effects left-to-right.
foldListT :: Monad m => (a -> m b -> m b) -> m b -> ListT m a -> m b
foldListT cons nil = loop where
  loop l = caseListT l nil $ \ a l' -> cons a $ loop l'

-- | Force all values in the lazy list, effects left-to-right
sequenceListT :: Monad m => ListT m a -> m [a]
sequenceListT = foldListT ((<$>) . (:)) $ pure []

-- | The join operation of the @ListT m@ monad.
concatListT :: Monad m => ListT m (ListT m a) -> ListT m a
concatListT = ListT . foldListT append (return Nothing)
  where append l = runListT . mappend l . ListT

-- * Monadic list operations.

-- | We can ``run'' a computation of a 'ListT' as it is monadic itself.
runMListT :: Monad m => m (ListT m a) -> ListT m a
runMListT ml = ListT $ runListT =<< ml

-- | Monadic cons.
consMListT :: Monad m => m a -> ListT m a -> ListT m a
consMListT ma l = ListT $ (Just . (,l)) `liftM` ma
-- consMListT ma l = runMListT $ liftM (`consListT` l) ma

-- simplification:
-- consMListT ma l = ListT $ runListT =<< liftM (`consListT` l) ma
-- consMListT ma l = ListT $ runListT =<< (`consListT` l) <$> ma
-- consMListT ma l = ListT $ runListT =<< do a <- ma; return $ a `consListT` l
-- consMListT ma l = ListT $ do a <- ma; runListT =<< do return $ a `consListT` l
-- consMListT ma l = ListT $ do a <- ma; runListT $ a `consListT` l
-- consMListT ma l = ListT $ do a <- ma; runListT $ ListT $ return $ Just (a, l)
-- consMListT ma l = ListT $ do a <- ma; return $ Just (a, l)
-- consMListT ma l = ListT $ Just . (,l) <$> ma

-- | Monadic singleton.
sgMListT ::  Monad m => m a -> ListT m a
sgMListT ma = consMListT ma nilListT

-- | Extending a monadic function to 'ListT'.
mapMListT :: Monad m => (a -> m b) -> ListT m a -> ListT m b
mapMListT f (ListT ml) = ListT $ do
  caseMaybeM ml (return Nothing) $ \ (a, as) -> do
    b  <- f a
    return $ Just (b , mapMListT f as)

-- | Alternative implementation using 'foldListT'.
mapMListT_alt :: Monad m => (a -> m b) -> ListT m a -> ListT m b
mapMListT_alt f = runMListT . foldListT cons (return nilListT)
  where cons a ml = consMListT (f a) <$> ml

-- | Change from one monad to another
liftListT :: (Monad m, Monad m') => (forall a. m a -> m' a) -> ListT m a -> ListT m' a
liftListT lift xs = runMListT $ caseMaybeM (lift $ runListT xs) (return nilListT) $
    \(x,xs) -> return $ consListT x $ liftListT lift xs

-- Instances

instance Monad m => Semigroup (ListT m a) where
  l1 <> l2 = ListT $ foldListT cons (runListT l2) l1
    where cons a = runListT . consListT a . ListT
instance Monad m => Monoid (ListT m a) where
  mempty        = nilListT
  mappend = (<>)

instance (Functor m, Applicative m, Monad m) => Alternative (ListT m) where
  empty = mempty
  (<|>) = mappend

instance (Functor m, Applicative m, Monad m) => MonadPlus (ListT m) where
  mzero = mempty
  mplus = mappend

instance (Functor m, Applicative m, Monad m) => Applicative (ListT m) where
  pure  = sgListT
  (<*>) = ap

  -- Another Applicative, but not the canonical one.
  -- l1 <*> l2 = ListT $ loop <$> runListT l1 <*> runListT l2
  --   where
  --   loop (Just (f, l1')) (Just (a, l2')) = Just (f a, l1' <*> l2')
  --   loop _ _ = Nothing

instance (Functor m, Applicative m, Monad m) => Monad (ListT m) where
  return  = pure
  l >>= k = concatListT $ k <$> l

instance MonadTrans ListT where
  lift = sgMListT

instance (Applicative m, MonadIO m) => MonadIO (ListT m) where
  liftIO = lift . liftIO

instance (Applicative m, MonadReader r m) => MonadReader r (ListT m) where
  ask     = lift ask
  local f = ListT . local f . runListT

instance (Applicative m, MonadState s m) => MonadState s (ListT m) where
  get = lift get
  put = lift . put

instance Monad m => MonadFail (ListT m) where
  fail _ = empty

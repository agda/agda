{-# LANGUAGE CPP #-}

module Agda.Utils.Monad
    ( module Agda.Utils.Monad
    , module X
    , (<$>), (<*>) , (<$)
    )
    where

import Control.Applicative    ( liftA2 )
import Control.Monad.Except   ( MonadError(catchError, throwError) )
import Control.Monad.Identity ( runIdentity )
import Control.Monad.State    ( MonadState(get, put) )
import Control.Monad.Writer   ( MonadWriter(tell), Writer, WriterT, mapWriterT )

import Data.Bifunctor         ( first, second )
import Data.Bool              ( bool )
import Data.Traversable as Trav hiding (for, sequence)
import Data.Foldable as Fold
import Data.Maybe
import Data.Monoid

import Agda.Utils.Applicative
import Agda.Utils.Boolean
import Agda.Utils.Either
import Agda.Utils.Null (empty, ifNotNullM)
import Agda.Utils.Singleton

import Agda.Utils.Impossible

-- Reexport Control.Monad
import Control.Monad as X
  ( MonadPlus(..), (<$!>), (>=>), (<=<)
  , filterM, foldM, forM, forM_
  , join
  , liftM2, liftM3, liftM4
  , msum
  , void
  , zipWithM, zipWithM_
  )
import Control.Monad.Trans as X
  ( MonadTrans, lift
  )


---------------------------------------------------------------------------
-- Vendor some new functions from mtl-2.3.1

#if MIN_VERSION_mtl(2,3,1)
import Control.Monad.Except as X ( tryError, withError )
#endif

#if !MIN_VERSION_mtl(2,3,1)
-- | 'MonadError' analogue to the 'Control.Exception.try' function.
tryError :: MonadError e m => m a -> m (Either e a)
tryError action = (Right <$> action) `catchError` (pure . Left)

-- | 'MonadError' analogue to the 'withExceptT' function.
-- Modify the value (but not the type) of an error.  The type is
-- fixed because of the functional dependency @m -> e@.  If you need
-- to change the type of @e@ use 'mapError' or 'modifyError'.
withError :: MonadError e m => (e -> e) -> m a -> m a
withError f action = tryError action >>= either (throwError . f) pure
#endif

---------------------------------------------------------------------------

-- | Binary bind.
(==<<) :: Monad m => (a -> b -> m c) -> (m a, m b) -> m c
k ==<< (ma, mb) = ma >>= \ a -> k a =<< mb

-- | Strict `ap`
(<*!>) :: Monad m => m (a -> b) -> m a -> m b
(<*!>) mf ma = do
  f <- mf
  a <- ma
  pure $! f a
{-# INLINE (<*!>) #-}
infixl 4 <*!>

-- Conditionals and monads ------------------------------------------------

{-# SPECIALIZE when :: Monad m => Bool -> m () -> m () #-}
when :: (IsBool b, Monad m) => b -> m () -> m ()
when b m = ifThenElse b m $ pure ()

{-# SPECIALIZE unless :: Monad m => Bool -> m () -> m () #-}
unless :: (IsBool b, Monad m) => b -> m () -> m()
unless b m = ifThenElse b (pure ()) m

{-# SPECIALIZE guard :: MonadPlus m => Bool -> m () #-}
guard :: (IsBool b, MonadPlus m) => b -> m ()
guard b = ifThenElse b (pure ()) mzero

whenM :: Monad m => m Bool -> m () -> m ()
whenM c m = c >>= (`when` m)

unlessM :: Monad m => m Bool -> m () -> m ()
unlessM c m = c >>= (`unless` m)

-- | Monadic guard.
guardM :: (Monad m, MonadPlus m) => m Bool -> m ()
guardM c = guard =<< c

-- | Monadic if-then-else.
ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM c m m' = c >>= \b -> if b then m else m'

-- | @ifNotM mc = ifM (not <$> mc)@
ifNotM :: Monad m => m Bool -> m a -> m a -> m a
ifNotM c = flip $ ifM c

-- | Lazy monadic conjunction.
and2M :: Monad m => m Bool -> m Bool -> m Bool
and2M ma mb = ifM ma mb (return False)

andM :: (Foldable f, Monad m) => f (m Bool) -> m Bool
andM = Fold.foldl' and2M (return True)

allM :: (Foldable f, Monad m) => f a -> (a -> m Bool) -> m Bool
allM xs f = Fold.foldl' (\b -> and2M b . f) (return True) xs

-- | Lazy monadic disjunction.
or2M :: Monad m => m Bool -> m Bool -> m Bool
or2M ma = ifM ma (return True)

orM :: (Foldable f, Monad m) => f (m Bool) -> m Bool
orM = Fold.foldl' or2M (return False)

anyM :: (Foldable f, Monad m) => f a -> (a -> m Bool) -> m Bool
anyM xs f = Fold.foldl' (\b -> or2M b . f) (return False) xs

-- | Lazy monadic disjunction with @Either@  truth values.
--   Returns the last error message if all fail.
altM1 :: Monad m => (a -> m (Either err b)) -> [a] -> m (Either err b)
altM1 f []       = __IMPOSSIBLE__
altM1 f [a]      = f a
altM1 f (a : as) = either (const $ altM1 f as) (return . Right) =<< f a

-- | Lazy monadic disjunction with accumulation of errors in a monoid.
--   Errors are discarded if we succeed.
orEitherM :: (Monoid e, Monad m, Functor m) => [m (Either e b)] -> m (Either e b)
orEitherM []       = return $ Left mempty
orEitherM (m : ms) = caseEitherM m (\e -> mapLeft (e `mappend`) <$> orEitherM ms)
                                   (return . Right)

-- Loops gathering results in a Monoid ------------------------------------

-- | Generalized version of @traverse_ :: Applicative m => (a -> m ()) -> [a] -> m ()@
--   Executes effects and collects results in left-to-right order.
--   Works best with left-associative monoids.
--
--   Note that there is an alternative
--
--     @mapM' f t = foldr mappend mempty <$> mapM f t@
--
--   that collects results in right-to-left order
--   (effects still left-to-right).
--   It might be preferable for right associative monoids.
mapM' :: (Foldable t, Applicative m, Monoid b) => (a -> m b) -> t a -> m b
mapM' f = Fold.foldl (\ mb a -> liftA2 mappend mb (f a)) (pure mempty)

-- | Generalized version of @for_ :: Applicative m => [a] -> (a -> m ()) -> m ()@
forM' :: (Foldable t, Applicative m, Monoid b) => t a -> (a -> m b) -> m b
forM' = flip mapM'

-- Variations of Traversable

mapMM :: (Traversable t, Monad m) => (a -> m b) -> m (t a) -> m (t b)
mapMM f mxs = Trav.mapM f =<< mxs

forMM :: (Traversable t, Monad m) => m (t a) -> (a -> m b) -> m (t b)
forMM = flip mapMM

-- Variations of Foldable

mapMM_ :: (Foldable t, Monad m) => (a -> m ()) -> m (t a) -> m ()
mapMM_ f mxs = Fold.mapM_ f =<< mxs

forMM_ :: (Foldable t, Monad m) => m (t a) -> (a -> m ()) -> m ()
forMM_ = flip mapMM_

-- Continuation monad -----------------------------------------------------

-- Andreas, 2017-04-11, issue #2543
-- The terribly useful thread function is now UNUSED.  [Sadistic laughter :)]
--
-- type Cont r a = (a -> r) -> r
--
-- -- | 'Control.Monad.mapM' for the continuation monad. Terribly useful.
-- thread :: (a -> Cont r b) -> [a] -> Cont r [b]
-- thread f [] ret = ret []
-- thread f (x:xs) ret =
--     f x $ \y -> thread f xs $ \ys -> ret (y:ys)

-- Lists and monads -------------------------------------------------------

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = concat <$> Trav.mapM f xs

-- | A monadic version of @'mapMaybe' :: (a -> Maybe b) -> [a] -> [b]@.
mapMaybeM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM f = go where
  go []     = return []
  go (a:as) = f a >>= \case
    Nothing -> go as
    Just b  -> do {!bs <- go as; pure (b : bs)}
{-# INLINE mapMaybeM #-}

-- | A version of @'mapMaybeM'@ with a computation for the input list.
mapMaybeMM :: Monad m => (a -> m (Maybe b)) -> m [a] -> m [b]
mapMaybeMM f m = mapMaybeM f =<< m
{-# INLINE mapMaybeMM #-}

-- | The @for@ version of 'mapMaybeM'.
forMaybeM :: Monad m => [a] -> (a -> m (Maybe b)) -> m [b]
forMaybeM = flip mapMaybeM

-- | The @for@ version of 'mapMaybeMM'.
forMaybeMM :: Monad m => m [a] -> (a -> m (Maybe b)) -> m [b]
forMaybeMM = flip mapMaybeMM

-- | A monadic version of @'dropWhile' :: (a -> Bool) -> [a] -> [a]@.
dropWhileM :: Monad m => (a -> m Bool) -> [a] -> m [a]
dropWhileM p []       = return []
dropWhileM p (x : xs) = ifM (p x) (dropWhileM p xs) (return (x : xs))

-- | A monadic version of @'dropWhileEnd' :: (a -> Bool) -> [a] -> m [a]@.
--   Effects happen starting at the end of the list until @p@ becomes false.
dropWhileEndM :: Monad m => (a -> m Bool) -> [a] -> m [a]
dropWhileEndM p []       = return []
dropWhileEndM p (x : xs) = ifNotNullM (dropWhileEndM p xs) (return . (x:)) $ {-else-}
  ifM (p x) (return []) (return [x])

-- | A ``monadic'' version of @'partition' :: (a -> Bool) -> [a] -> ([a],[a])
partitionM :: (Functor m, Applicative m) => (a -> m Bool) -> [a] -> m ([a], [a])
partitionM f =
  foldr (\ x -> liftA2 (bool (second (x:)) (first (x:))) $ f x)
        (pure empty)

-- MonadPlus -----------------------------------------------------------------

-- | Translates 'Maybe' to 'MonadPlus'.
fromMaybeMP :: MonadPlus m => Maybe a -> m a
fromMaybeMP = foldA

-- | Generalises the 'catMaybes' function from lists to an arbitrary
-- 'MonadPlus'.
catMaybesMP :: MonadPlus m => m (Maybe a) -> m a
catMaybesMP = scatterMP

-- | Branch over elements of a monadic 'Foldable' data structure.
scatterMP :: (MonadPlus m, Foldable t) => m (t a) -> m a
scatterMP = (>>= foldA)


-- Error monad ------------------------------------------------------------

-- | Finally for the 'Error' class. Errors in the finally part take
-- precedence over prior errors.

finally :: MonadError e m => m a -> m () -> m a
first `finally` after = do
  r <- catchError (fmap Right first) (return . Left)
  after
  case r of
    Left e  -> throwError e
    Right r -> return r

-- | Try a computation, return 'Nothing' if an 'Error' occurs.

tryMaybe :: (MonadError e m, Functor m) => m a -> m (Maybe a)
tryMaybe m = (Just <$> m) `catchError` \ _ -> return Nothing

-- | Run a command, catch the exception and return it.

tryCatch :: (MonadError e m, Functor m) => m () -> m (Maybe e)
tryCatch m = (Nothing <$ m) `catchError` \ err -> return $ Just err

-- | Like 'guard', but raise given error when condition fails.

guardWithError :: MonadError e m => e -> Bool -> m ()
guardWithError e b = if b then return () else throwError e

-- State monad ------------------------------------------------------------

-- | Bracket without failure.  Typically used to preserve state.
bracket_ :: Monad m
         => m a         -- ^ Acquires resource. Run first.
         -> (a -> m ())  -- ^ Releases resource. Run last.
         -> m b         -- ^ Computes result. Run in-between.
         -> m b
bracket_ acquire release compute = do
  resource <- acquire
  result <- compute
  release resource
  return result

-- | Restore state after computation.
localState :: MonadState s m => m a -> m a
localState = bracket_ get put

-- Writer monad -----------------------------------------------------------

embedWriter :: (Monoid w, Monad m) => Writer w a -> WriterT w m a
embedWriter = mapWriterT (pure . runIdentity)

-- | Output a single value.
tell1 :: (Monoid ws, Singleton w ws, MonadWriter ws m) => w -> m ()
tell1 = tell . singleton

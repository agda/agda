
module Agda.Utils.Monad
    ( module Agda.Utils.Monad
    , when, unless, MonadPlus(..)
    , (<$>), (<*>)
    , (<$)
    )
    where

import Control.Applicative  ( liftA2 )
import Control.Monad        ( MonadPlus(..), guard, unless, when )
import Control.Monad.Except ( MonadError(catchError, throwError) )
import Control.Monad.State  ( MonadState(get, put) )

import Data.Bifunctor       ( first, second )
import Data.Bool            ( bool )
import Data.Traversable as Trav hiding (for, sequence)
import Data.Foldable as Fold
import Data.Maybe
import Data.Monoid

import Agda.Utils.Applicative
import Agda.Utils.Either
import Agda.Utils.Null (empty, ifNotNullM)

import Agda.Utils.Impossible

---------------------------------------------------------------------------

-- | Binary bind.
(==<<) :: Monad m => (a -> b -> m c) -> (m a, m b) -> m c
k ==<< (ma, mb) = ma >>= \ a -> k a =<< mb

-- Conditionals and monads ------------------------------------------------

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
andM = Fold.foldl and2M (return True)

allM :: (Functor f, Foldable f, Monad m) => f a -> (a -> m Bool) -> m Bool
allM xs f = andM $ fmap f xs

-- | Lazy monadic disjunction.
or2M :: Monad m => m Bool -> m Bool -> m Bool
or2M ma = ifM ma (return True)

orM :: (Foldable f, Monad m) => f (m Bool) -> m Bool
orM = Fold.foldl or2M (return False)

anyM :: (Functor f, Foldable f, Monad m) => f a -> (a -> m Bool) -> m Bool
anyM xs f = orM $ fmap f xs

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

-- | A monadic version of @'mapMaybe' :: (a -> Maybe b) -> [a] -> [b]@.
mapMaybeM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM f xs = catMaybes <$> Trav.mapM f xs

-- | A version of @'mapMaybeM'@ with a computation for the input list.
mapMaybeMM :: Monad m => (a -> m (Maybe b)) -> m [a] -> m [b]
mapMaybeMM f m = mapMaybeM f =<< m

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
  foldr (\ x mlr -> bool (first (x:)) (second (x:)) <$> f x <*> mlr)
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

{-# LANGUAGE CPP, FlexibleContexts #-}

module Agda.Utils.Monad
    ( module Agda.Utils.Monad
{- Andreas 2012-04-21: I'd like to reexport Control.Monad except
   patching when and unless, but the hiding syntax is not valid yet
   (only a proposed language extension)

    , module Control.Monad hiding (when, unless)
-}
    , (<$>), (<*>)
    )
    where

import Prelude		   hiding (concat)
import Control.Monad
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import qualified Control.Monad.State.Strict as SS
import Control.Monad.Writer
import Control.Applicative
import Data.Traversable as Trav hiding (sequence)
import Data.Foldable as Fold
import Data.Monoid
import Data.Maybe

import Agda.Utils.List

#include "../undefined.h"
import Agda.Utils.Impossible

-- Conditionals and monads ------------------------------------------------

-- | @when_@ is just @Control.Monad.when@ with a more general type.
when_ :: Monad m => Bool -> m a -> m ()
when_ b m = when b $ do m >> return ()

-- | @unless_@ is just @Control.Monad.unless@ with a more general type.
unless_ :: Monad m => Bool -> m a -> m ()
unless_ b m = unless b $ do m >> return ()

whenJust :: Monad m => Maybe a -> (a -> m ()) -> m ()
whenJust m k = flip (maybe $ return ()) m k

whenM :: Monad m => m Bool -> m a -> m ()
whenM c m = c >>= (`when_` m)

unlessM :: Monad m => m Bool -> m a -> m ()
unlessM c m = c >>= (`unless_` m)

whenJustM :: Monad m => m (Maybe a) -> (a -> m ()) -> m ()
whenJustM c m = c >>= (`whenJust` m)

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM c m m' =
    do	b <- c
	if b then m else m'

-- | Lazy monadic conjunction.
and2M :: Monad m => m Bool -> m Bool -> m Bool
and2M ma mb = ifM ma mb (return False)

andM :: Monad m => [m Bool] -> m Bool
andM = Fold.foldl and2M (return True)

-- | Lazy monadic disjunction.
or2M :: Monad m => m Bool -> m Bool -> m Bool
or2M ma mb = ifM ma (return True) mb

orM :: Monad m => [m Bool] -> m Bool
orM = Fold.foldl or2M (return False)

-- | Lazy monadic disjunction with @Either@  truth values.
altM1 :: Monad m => (a -> m (Either err b)) -> [a] -> m (Either err b)
altM1 f []       = __IMPOSSIBLE__
altM1 f [a]      = f a
altM1 f (a : as) = either (const $ altM1 f as) (return . Right) =<< f a

-- Loops gathering results in a Monoid ------------------------------------

-- | Generalized version of @mapM_ :: Monad m => (a -> m ()) -> [a] -> m ()@
--   Executes effects and collects results in left-to-right order.
--   Works best with left-associative monoids.
--
--   Note that there is an alternative
--
--     @mapM' f t = foldr mappend mempty <$> mapM f t@
--
--   that collects results in right-to-left order (effects still right-to-left).
--   It might be preferable for right associative monoids.
mapM' :: (Foldable t, Monad m, Monoid b) => (a -> m b) -> t a -> m b
mapM' f = Fold.foldl (\ mb a -> liftM2 mappend mb (f a)) (return mempty)

-- | Generalized version of @forM_ :: Monad m => [a] -> (a -> m ()) -> m ()@
forM' :: (Foldable t, Monad m, Monoid b) => t a -> (a -> m b) -> m b
forM' = flip mapM'

-- Continuation monad -----------------------------------------------------

type Cont r a = (a -> r) -> r

-- | 'Control.Monad.mapM' for the continuation monad. Terribly useful.
thread :: (a -> Cont r b) -> [a] -> Cont r [b]
thread f [] ret = ret []
thread f (x:xs) ret =
    f x $ \y -> thread f xs $ \ys -> ret (y:ys)

-- Lists and monads -------------------------------------------------------

-- | Requires both lists to have the same lengths.
zipWithM' :: Monad m => (a -> b -> m c) -> [a] -> [b] -> m [c]
zipWithM' f xs ys = sequence (zipWith' f xs ys)

-- | A monadic version of @mapMaybe :: (a -> Maybe b) -> [a] -> [b]@.
mapMaybeM :: (Monad m, Functor m) => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM f xs = catMaybes <$> Trav.mapM f xs

-- Error monad ------------------------------------------------------------

-- | Finally for the 'Error' class. Errors in the finally part take
-- precedence over prior errors.

finally :: (Error e, MonadError e m) => m a -> m b -> m a
first `finally` after = do
  r <- catchError (liftM Right first) (return . Left)
  after
  case r of
    Left e  -> throwError e
    Right r -> return r

-- | Bracket for the 'Error' class.

bracket :: (Error e, MonadError e m)
        => m a         -- ^ Acquires resource. Run first.
        -> (a -> m c)  -- ^ Releases resource. Run last.
        -> (a -> m b)  -- ^ Computes result. Run in-between.
        -> m b
bracket acquire release compute = do
  resource <- acquire
  compute resource `finally` release resource

-- State monad ------------------------------------------------------------

-- | Bracket without failure.  Typically used to preserve state.
bracket_ :: (Monad m)
         => m a         -- ^ Acquires resource. Run first.
         -> (a -> m c)  -- ^ Releases resource. Run last.
         -> m b         -- ^ Computes result. Run in-between.
         -> m b
bracket_ acquire release compute = do
  resource <- acquire
  result <- compute
  release resource
  return result

-- | Restore state after computation.
localState :: (MonadState s m) => m a -> m a
localState = bracket_ get put

-- Read -------------------------------------------------------------------

readM :: (Error e, MonadError e m, Read a) => String -> m a
readM s = case reads s of
	    [(x,"")]	-> return x
	    _		->
              throwError $ strMsg $ "readM: parse error string " ++ s




-- RETIRED STUFF ----------------------------------------------------------


{- Andreas 2012-04-21: <.> is obsolete, it is called <=< in Control.Monad
infixl 8 <.>

(<.>) :: Monad m => (b -> m c) -> (a -> m b) -> a -> m c
f <.> g = \x -> f =<< g x
-}

{- RETIRED, Andreas, 2012-04-30.
   For GHC >= 7, there is now Control.Monad.void.
forgetM :: Applicative m => m a -> m ()
forgetM m = const () <$> m
-}

{- RETIRED, Andreas, 2012-04-30. Not used.
concatMapM :: Applicative m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = concat <$> traverse f xs

-- | Depending on the monad you have to look at the result for
--   the force to be effective. For the 'IO' monad you do.
forceM :: Monad m => [a] -> m ()
forceM xs = do () <- length xs `seq` return ()
	       return ()

commuteM :: (Traversable f, Applicative m) => f (m a) -> m (f a)
commuteM = traverse id

-- these are just instances of traverse:

fmapM :: (Traversable f, Applicative m) => (a -> m b) -> f a -> m (f b)
fmapM f = commuteM . fmap f

mapMaybeM :: Applicative m => (a -> m b) -> Maybe a -> m (Maybe b)
mapMaybeM f = maybe (pure Nothing) (\x -> Just <$> f x)

-}

{- UNUSED

-- Either -----------------------------------------------------------------

liftEither :: MonadError e m => Either e a -> m a
liftEither = either throwError return
-}

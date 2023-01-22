module Agda.Interaction.Widget
  ( MonadStatic(..)

  , StaticT
  -- * Rendering from 'StaticT'
  , renderStaticT

  -- * Rendering widgets
  , MonadWidget
  , ToWidget(..)

  -- * Widget utilities
  , cycleTrigger, cycleBetween, cycleBetween', eagerly
  )
  where

import Prelude hiding ( null )

import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Monad.Closure
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Pure
import Agda.TypeChecking.Monad.Base

import Agda.TypeChecking.Pretty

import qualified Agda.Utils.Pretty.Aspect as P
import qualified Agda.Utils.Pretty as P
import qualified Agda.Utils.List1 as L1
import Agda.Utils.List1 (List1, NonEmpty((:|)))
import Agda.Utils.Monad

import qualified Control.Monad.State as Lazy
import Control.Monad.Trans.Control
import Control.Monad.State.Strict

import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)
import Data.IORef
import Data.Kind

-- | A monad which supports “phase separation”, used for rendering
-- widgets.
class (Monad m, Monad (Dynamic m)) => MonadStatic m where
  -- | A monad of 'Dynamic' values, associated to each instance of
  -- 'MonadDynamic'.
  type Dynamic m  :: Type -> Type

  -- | A token type representing event triggers.
  data Trigger m

  -- | Create a new 'Dynamic' with the given initial value. When
  -- returned the 'Trigger' is invoked, the value should be updated
  -- according to the given function.
  newDynamic     :: a -> (a -> a) -> m (Dynamic m a, Trigger m)

  -- | Attach an event trigger to a dynamic document. The trigger should
  -- be invoked whenever the document is clicked.
  triggerOnClick :: Trigger m -> Dynamic m Doc -> Dynamic m Doc

data DynState
  = DynState
    { dynNextTrigger :: {-# UNPACK #-} !Int
    , dynActions     :: IntMap (IO ())
    }

-- | Equip arbitrary instances of 'MonadIO' with a phase distinction.
-- The given monad is reused as the monad of 'Dynamic' values.
newtype StaticT m a = StaticT { getDynamic :: StateT DynState m a }
  deriving (Functor, Applicative, Monad, MonadIO)

runStaticT :: StaticT m a -> DynState -> m (a, DynState)
runStaticT = runStateT . getDynamic

-- StaticT works by using IORefs in the underlying monad.
--
-- Triggers are represented as just integers, since that's what the
-- Emacs mode thinks callbacks are.
--
-- "Rendering" a StaticT produces a table associating integers to @IO
-- ()@ actions which perform the associated update.
--
-- The "dynamic value" which 'newDynamic' creates is just the action of
-- reading the underlying IORef.

instance MonadIO m => MonadStatic (StaticT m) where
  data Trigger (StaticT m) = Trigger
    { triggerId :: {-# UNPACK #-} !Int }

  type Dynamic (StaticT m)    = m

  newDynamic init upd = do
    t <- liftIO $ newIORef init
    let act = modifyIORef' t upd
    id <- StaticT $ state $ \x ->
      let id = dynNextTrigger x in
      ( id
      , x { dynNextTrigger = id + 1
          , dynActions     = IntMap.insert id act (dynActions x)
          }
      )
    pure (liftIO (readIORef t), Trigger id)

  triggerOnClick (Trigger i) a =
    fmap (P.withAspect (P.TriggerCallback i)) a

renderStaticT
  :: Monad m
  => StaticT m (Dynamic (StaticT m) a)
  -> m (IntMap (IO ()), m a)
renderStaticT (StaticT k) = do
  (a, s) <- runStateT k (DynState 0 mempty)
  pure (dynActions s, a)

-- | Given a list of values, create a 'Dynamic' that cycles between, and
-- return the trigger.
cycleTrigger
  :: MonadStatic m
  => List1 a
  -> m (Dynamic m a, Trigger m)
cycleTrigger choices = do
  let
    rotate (x :| [])     = x :| []
    rotate (x :| (y:xs)) = y :| (xs ++ [x])
  (t, trigger) <- newDynamic choices rotate
  pure (L1.head <$> t, trigger)

-- | Like 'cycleTrigger', but associate the trigger with the selected
-- value.
cycleBetween :: MonadStatic m => List1 (Dynamic m Doc) -> m (Dynamic m Doc)
cycleBetween xs = do
  (m, t) <- cycleTrigger xs
  pure (triggerOnClick t =<< m)

-- | Like 'cycleBetween', but panicking on an empty list.
cycleBetween' :: MonadStatic m => [Dynamic m Doc] -> m (Dynamic m Doc)
cycleBetween' []     = error "Widget.cycleBetween': Empty list"
cycleBetween' (x:xs) = cycleBetween (x :| xs)

-- | Given a rendering action which works for arbitrary 'MonadPretty'
-- instances (e.g.: 'prettyTCM'), pre-compute the 'Doc' and return an
-- unchanging 'Dynamic' value.
eagerly :: MonadWidget m'
        => (forall m. MonadPretty m => m Doc)
        -> m' (Dynamic m' Doc)
eagerly a = do
  t <- liftTCM a
  pure (pure t)

-- | A monad which is proper for rendering dynamic widgets. Every
-- 'MonadWidget' is a 'MonadStatic' whose associated monad of 'Dynamic'
-- values is a 'MonadPretty'; This means that 'PrettyTCM' can be used
-- for dynamic rendering. Furthermore, every 'MonadWidget' supports the
-- 'PureTCM' interface and can embed 'TCM' computations using
-- 'MonadTCM'.
type MonadWidget m = (MonadStatic m, PureTCM m, MonadTCM m, MonadPretty (Dynamic m))

-- | Types which can be rendered into a widget.
class ToWidget a where
  toWidget :: forall m. MonadWidget m => a -> m (Dynamic m Doc)

instance ToWidget a => ToWidget (Closure a) where
  toWidget cl = enterClosure cl $ \a -> do
    t <- toWidget a
    -- Must re-enter closure when rendering:
    pure $ enterClosure cl (const t)

-- StaticT needs to have a gajillion instances to use usable in
-- rendering; most of them are default.

deriving instance MonadTrans StaticT
deriving instance MonadFail m     => MonadFail (StaticT m)
instance MonadFresh a m           => MonadFresh a (StaticT m)
instance HasBuiltins m            => HasBuiltins (StaticT m)
instance HasConstInfo m           => HasConstInfo (StaticT m)
instance MonadAddContext m        => MonadAddContext (StaticT m)
instance MonadDebug m             => MonadDebug (StaticT m)
instance MonadReduce m            => MonadReduce (StaticT m)
instance MonadTCEnv m             => MonadTCEnv (StaticT m)
instance MonadTCState m           => MonadTCState (StaticT m)
instance ReadTCState m            => ReadTCState (StaticT m)
instance PureTCM m                => PureTCM (StaticT m)
instance HasOptions m             => HasOptions (StaticT m)
instance MonadInteractionPoints m => MonadInteractionPoints (StaticT m)

instance MonadTransControl StaticT where
  type StT StaticT a = (a, DynState)
  liftWith f = StaticT $ StateT $ \s ->
                  liftM (\x -> (x, s))
                        (f $ \t -> runStateT (getDynamic t) s)
  restoreT = StaticT . StateT . const
  {-# INLINABLE liftWith #-}
  {-# INLINABLE restoreT #-}

instance MonadStConcreteNames m   => MonadStConcreteNames (StaticT m) where
  runStConcreteNames m = StaticT $ StateT $ \s -> runStConcreteNames $ Lazy.StateT $ \ns -> do
    ((x, ns'), s') <- runStaticT (Lazy.runStateT m ns) s
    return ((x, s'), ns')
instance MonadTCM m => MonadTCM (StaticT m)

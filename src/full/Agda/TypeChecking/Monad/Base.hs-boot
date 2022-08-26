{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Base where

import Control.Monad.Trans.Control
import Control.Monad.Trans
import Control.Monad.IO.Class (MonadIO)
import Data.IORef (IORef)
import Data.Map (Map)

import Agda.Syntax.Common (Nat, InteractionId)
import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)
import Agda.Utils.FileName (AbsolutePath)
import Agda.Syntax.Internal
import Control.Monad.State
import qualified Agda.Syntax.Concrete as C
import Agda.Utils.Lens
import Agda.Utils.BiMap
import Agda.Interaction.Options.HasOptions

data Warning

data TCErr
data TCWarning
data NamedMeta
data HighlightingMethod
instance Show HighlightingMethod
instance Read HighlightingMethod

data HighlightingLevel
instance Show HighlightingLevel
instance Read HighlightingLevel


data TCEnv
data TCState
newtype TCMT m a = TCM { unTCM :: IORef TCState -> TCEnv -> m a }

instance Applicative m => Applicative (TCMT m)
instance Functor m => Functor (TCMT m)
instance MonadIO m => MonadIO (TCMT m)

#if __GLASGOW_HASKELL__ < 808
instance MonadIO m => Monad (TCMT m) where
#else
-- Andreas, 2022-02-02, issue #5659:
-- @transformers-0.6@ requires exactly a @Monad@ superclass constraint here
-- if we want @instance MonadTrans TCMT@.
instance Monad m => Monad (TCMT m) where
#endif

type TCM = TCMT IO

type ModuleToSource = Map TopLevelModuleName AbsolutePath

type BackendName = String

data Comparison
data Polarity

type Context      = [ContextEntry]
type ContextEntry = Dom (Name, Type)

class Monad m => MonadFresh i m where
  fresh :: m i

  default fresh :: (MonadTrans t, MonadFresh i n, t n ~ m) => m i
  fresh = lift fresh

class Monad m => MonadTCEnv m where
  askTC   :: m TCEnv
  localTC :: (TCEnv -> TCEnv) -> m a -> m a

  default askTC :: (MonadTrans t, MonadTCEnv n, t n ~ m) => m TCEnv
  askTC = lift askTC

  default localTC
    :: (MonadTransControl t, MonadTCEnv n, t n ~ m)
    =>  (TCEnv -> TCEnv) -> m a -> m a
  localTC = liftThrough . localTC

data Closure a

type ConcreteNames = Map Name [C.Name]

class Monad m => MonadStConcreteNames m where
  runStConcreteNames :: StateT ConcreteNames m a -> m a

  useConcreteNames :: m ConcreteNames
  useConcreteNames = runStConcreteNames get

  modifyConcreteNames :: (ConcreteNames -> ConcreteNames) -> m ()
  modifyConcreteNames = runStConcreteNames . modify

data DisplayTerm

data PrimFun
data Builtin pf
newtype CheckpointId = CheckpointId Int

class Monad m => ReadTCState m where
  getTCState :: m TCState
  locallyTCState :: Lens' a TCState -> (a -> a) -> m b -> m b

  withTCState :: (TCState -> TCState) -> m a -> m a
  withTCState = locallyTCState id

  default getTCState :: (MonadTrans t, ReadTCState n, t n ~ m) => m TCState
  getTCState = lift getTCState

  default locallyTCState
    :: (MonadTransControl t, ReadTCState n, t n ~ m)
    => Lens' a TCState -> (a -> a) -> m b -> m b
  locallyTCState l = liftThrough . locallyTCState l

data InteractionPoint
type InteractionPoints = BiMap InteractionId InteractionPoint
data Definition
data RewriteRule
type RewriteRules = [RewriteRule]

data ReduceEnv
newtype ReduceM a = ReduceM { unReduceM :: ReduceEnv -> a }
class ( Applicative m
      , MonadTCEnv m
      , ReadTCState m
      , HasOptions m
      ) => MonadReduce m where
  liftReduce :: ReduceM a -> m a

  default liftReduce :: (MonadTrans t, MonadReduce n, t n ~ m) => ReduceM a -> m a
  liftReduce = lift . liftReduce

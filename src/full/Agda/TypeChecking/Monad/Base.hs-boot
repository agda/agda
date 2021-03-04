{-# LANGUAGE TypeFamilies               #-} -- for type equality ~
{-# LANGUAGE RoleAnnotations            #-}
{-# LANGUAGE CPP                        #-}

module Agda.TypeChecking.Monad.Base where

import Control.Applicative (Const(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans          ( MonadTrans )
import Control.Monad.Trans.Control  ( MonadTransControl )
import Data.IORef (IORef)
import qualified Data.Kind
import Data.Map (Map)

import Agda.Syntax.Common (Nat, ProblemId)
import Agda.Syntax.Internal (Dom, Name, Term, Type)
import Agda.Syntax.Concrete.Name (TopLevelModuleName)
import Agda.Utils.FileName (AbsolutePath)
import Agda.Utils.IntSet.Typed (ISet)

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

instance MonadIO m => Applicative (TCMT m)
instance MonadIO m => Functor (TCMT m)
instance MonadIO m => Monad (TCMT m)
instance MonadIO m => MonadIO (TCMT m)

type TCM = TCMT IO

type ModuleToSource = Map TopLevelModuleName AbsolutePath

type BackendName = String

data Comparison
data Polarity
newtype CheckpointId = CheckpointId Int

class Monad m => MonadTCEnv m where
  askTC   :: m TCEnv
  localTC :: (TCEnv -> TCEnv) -> m a -> m a

  default askTC :: (MonadTrans t, MonadTCEnv n, t n ~ m) => m TCEnv
  askTC = lift askTC

  default localTC
    :: (MonadTransControl t, MonadTCEnv n, t n ~ m)
    =>  (TCEnv -> TCEnv) -> m a -> m a
  localTC = liftThrough . localTC

#if __GLASGOW_HASKELL__ <= 802
type role TwinT'' representational nominal
#endif
data TwinT'' b a =
    SingleT { unSingleT :: Het 'Both a }
  | TwinT { twinPid    :: ISet ProblemId
          , necessary  :: b
          , direction  :: CompareDirection
          , twinLHS    :: Het 'LHS a
          , twinRHS    :: Het 'RHS a
          }

type TwinT' = TwinT'' Bool
type TwinT = TwinT' Type
data ContextHet' a
type ContextHet = ContextHet' (Dom (Name, TwinT))

data ContextSide = LHS | RHS | Both | Compat | Single
newtype Het (side :: ContextSide) t = Het { unHet :: t }
instance Functor (Het side)

data CompareDirection

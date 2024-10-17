module Agda.TypeChecking.Monad.Base where

import Control.Monad.IO.Class (MonadIO)
import Data.IORef (IORef)

data Definition
data Warning

data TCErr
data TCWarning

data TCEnv
data TCState
newtype TCMT m a = TCM { unTCM :: IORef TCState -> TCEnv -> m a }

instance Applicative m => Applicative (TCMT m)
instance Functor m => Functor (TCMT m)
instance MonadIO m => MonadIO (TCMT m)

-- Andreas, 2022-02-02, issue #5659:
-- @transformers-0.6@ requires exactly a @Monad@ superclass constraint here
-- if we want @instance MonadTrans TCMT@.
instance Monad m => Monad (TCMT m) where

type TCM = TCMT IO

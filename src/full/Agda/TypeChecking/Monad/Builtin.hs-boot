
module Agda.TypeChecking.Monad.Builtin where

import Control.Monad.IO.Class       ( MonadIO )
import Control.Monad.Reader         ( ReaderT )
import Control.Monad.State          ( StateT )
import Control.Monad.Trans.Identity ( IdentityT )
import Control.Monad.Trans          ( MonadTrans, lift )

import qualified Control.Monad.Fail as Fail

import Agda.TypeChecking.Monad.Base (TCMT, Builtin, PrimFun)

class ( Functor m
      , Applicative m
      , Fail.MonadFail m
      ) => HasBuiltins m where
  getBuiltinThing :: String -> m (Maybe (Builtin PrimFun))
  default getBuiltinThing :: (MonadTrans t, HasBuiltins n, t n ~ m) => String -> m (Maybe (Builtin PrimFun))
  getBuiltinThing = lift . getBuiltinThing

instance HasBuiltins m => HasBuiltins (IdentityT m)
instance HasBuiltins m => HasBuiltins (ReaderT e m)
instance HasBuiltins m => HasBuiltins (StateT s m)

instance MonadIO m => HasBuiltins (TCMT m)

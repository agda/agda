
module Agda.TypeChecking.Monad.Builtin where

import Control.Monad.IO.Class       ( MonadIO )
import Control.Monad.Reader         ( ReaderT )
import Control.Monad.State          ( StateT )
import Control.Monad.Trans.Identity ( IdentityT )
import Control.Monad.Trans          ( MonadTrans, lift )

import Agda.TypeChecking.Monad.Base (TCMTC, Builtin, PrimFun)
import Agda.Syntax.Builtin (SomeBuiltin)

class ( Functor m
      , Applicative m
      , Monad m
      ) => HasBuiltins m where
  getBuiltinThing :: SomeBuiltin -> m (Maybe (Builtin PrimFun))
  default getBuiltinThing :: (MonadTrans t, HasBuiltins n, t n ~ m) => SomeBuiltin -> m (Maybe (Builtin PrimFun))
  getBuiltinThing = lift . getBuiltinThing

instance HasBuiltins m => HasBuiltins (IdentityT m)
instance HasBuiltins m => HasBuiltins (ReaderT e m)
instance HasBuiltins m => HasBuiltins (StateT s m)

instance MonadIO m => HasBuiltins (TCMTC c m)

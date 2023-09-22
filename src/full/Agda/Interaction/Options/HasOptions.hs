{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Interaction.Options.HasOptions
  ( HasOptions (pragmaOptions, commandLineOptions)
  ) where

import Control.Monad.Except (ExceptT)
import Control.Monad.Reader (ReaderT)
import Control.Monad.State (StateT)
import Control.Monad.Trans ( MonadTrans, lift )
import Control.Monad.Trans.Identity (IdentityT)
import Control.Monad.Trans.Maybe (MaybeT)
import Control.Monad.Writer (WriterT)

import Agda.Interaction.Options.Base (PragmaOptions, CommandLineOptions)
import Agda.Utils.Update (ChangeT)
import Agda.Utils.ListT (ListT)

class (Functor m, Applicative m, Monad m) => HasOptions m where
  -- | Returns the pragma options which are currently in effect.
  pragmaOptions      :: m PragmaOptions
  -- | Returns the command line options which are currently in effect.
  commandLineOptions :: m CommandLineOptions

  default pragmaOptions :: (HasOptions n, MonadTrans t, m ~ t n) => m PragmaOptions
  pragmaOptions      = lift pragmaOptions

  default commandLineOptions :: (HasOptions n, MonadTrans t, m ~ t n) => m CommandLineOptions
  commandLineOptions = lift commandLineOptions

-- HasOptions lifts through monad transformers
-- (see default signatures in the HasOptions class).

instance HasOptions m => HasOptions (ChangeT m)
instance HasOptions m => HasOptions (ExceptT e m)
instance HasOptions m => HasOptions (IdentityT m)
instance HasOptions m => HasOptions (ListT m)
instance HasOptions m => HasOptions (MaybeT m)
instance HasOptions m => HasOptions (ReaderT r m)
instance HasOptions m => HasOptions (StateT s m)
instance (HasOptions m, Monoid w) => HasOptions (WriterT w m)

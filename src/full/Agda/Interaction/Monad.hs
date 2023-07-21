{-# OPTIONS_GHC -Wunused-imports #-}

{-# OPTIONS_GHC -fwarn-orphans #-}
{-# LANGUAGE CPP               #-}

module Agda.Interaction.Monad
  ( IM
  , runIM
  , readline
  ) where

import Agda.TypeChecking.Monad
  ( HasOptions
  , MonadTCEnv
  , MonadTCM
  , MonadTCState
  , ReadTCState
  , TCErr
  , TCM, TCMT(..)
  , mapTCMT
  )
import Control.Exception (throwIO)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Trans (MonadIO, lift, liftIO)
import qualified System.Console.Haskeline as Haskeline

-- MonadException is replaced by MonadCatch in haskeline 0.8
#if MIN_VERSION_haskeline(0,8,0)
import qualified Control.Monad.Catch as Haskeline (catch)
#endif

-- | Interaction monad.
newtype IM a = IM {unIM :: TCMT (Haskeline.InputT IO) a}
  deriving
  ( Functor, Applicative, Monad, MonadIO
  , HasOptions, MonadTCEnv, ReadTCState, MonadTCState, MonadTCM )

runIM :: IM a -> TCM a
runIM = mapTCMT (Haskeline.runInputT Haskeline.defaultSettings) . unIM

instance MonadError TCErr IM where
  throwError                = liftIO . throwIO
  catchError (IM (TCM m)) h = IM . TCM $ \s e ->
    m s e `Haskeline.catch` \err -> unTCM (unIM (h err)) s e

-- | Line reader. The line reader history is not stored between
-- sessions.
readline :: String -> IM (Maybe String)
readline s = IM $ lift (Haskeline.getInputLine s)

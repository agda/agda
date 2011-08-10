{-# LANGUAGE TypeSynonymInstances, FlexibleInstances,
             MultiParamTypeClasses #-}
module Agda.Interaction.Monad where

import Agda.TypeChecking.Monad

import Control.Monad.Trans
import Control.Monad.Error
import System.Console.Haskeline

-- | Interaction monad.

type IM = TCMT (InputT IO)

instance MonadError TCErr IM where
  throwError = liftIO . throwIO
  catchError m h = mapTCMT liftIO $ runIM m `catchError` (runIM . h)

-- | Line reader. The line reader history is not stored between
-- sessions.

readline :: String -> IM (Maybe String)
readline s = lift (getInputLine s)

runIM :: IM a -> TCM a
runIM = mapTCMT (runInputT defaultSettings)

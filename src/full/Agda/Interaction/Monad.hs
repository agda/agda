
module Agda.Interaction.Monad where

import Agda.TypeChecking.Monad

import Control.Monad.Trans
import System.Console.Haskeline

-- | Interaction monad.

type IM = TCMT (InputT IO)

-- | Line reader. The line reader history is not stored between
-- sessions.

readline :: String -> IM (Maybe String)
readline s = lift (getInputLine s)

runIM :: IM a -> TCM a
runIM = mapTCMT (runInputT defaultSettings)

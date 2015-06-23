module Agda.Interaction.Monad (IM, runIM, readline) where

import Control.Monad.Trans
import System.Console.Haskeline

import Agda.TypeChecking.Monad

-- | Line reader. The line reader history is not stored between
-- sessions.

readline :: String -> IM (Maybe String)
readline s = lift (getInputLine s)

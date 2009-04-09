
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

{-
data CurrentPoint = InInteractionPoint InteractionId | TopLevel

newtype IM a = IM {unIM :: StateT [CurrentPoint] TCM a}
   deriving (Monad,MonadIO)


instance MonadError e IM where
    throwError	   = lift . throwError
    catchError m h = IM $ catchError (unIM m) (unIM . h)



instance MonadUndo [CurrentPoint] IM where
    undo =


run

-}

-- instance MonadTCM IM where
--     liftTCM = id

runIM :: IM a -> TCM a
runIM = mapTCMT (runInputT defaultSettings)

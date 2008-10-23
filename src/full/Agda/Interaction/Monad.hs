
module Agda.Interaction.Monad where

import Agda.TypeChecking.Monad
import Control.Monad.State
import Control.Monad.Error
import Agda.Utils.Monad.Undo

type IM = TCM 

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

runIM :: IM a -> IO (Either TCErr a)
runIM = runTCM


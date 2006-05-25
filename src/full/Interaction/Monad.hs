{-# OPTIONS -fglasgow-exts  #-}
module Interaction.Monad where

import TypeChecking.Monad
import Control.Monad.Error
import Utils.Monad.Undo

type IM = TCM 

{-
data CurrentPoint = InInteractionPoint InteractionPoint | TopLevel

newtype IM a = IM {unIM :: StateT [CurrentPoint] TCM}

instance MonadUndo [CurrentPoint] IM where
    undo (IM s) 
-}
liftTCM :: TCM a -> IM a 
liftTCM s = s

runIM :: IM a -> IO (Either TCErr a)
runIM = runTCM


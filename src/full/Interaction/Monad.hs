{-# OPTIONS -fglasgow-exts  #-}
module Interaction.Monad where

import TypeChecking.Monad
import Control.Monad.Error
import Utils.Monad.Undo

type IM = TCM

liftTCM :: TCM a -> IM a
liftTCM s = s

runIM :: IM a -> IO (Either TCErr a)
runIM = runTCM


{-# OPTIONS -fglasgow-exts  #-}
module Interaction.Monad where

import TypeChecking.Monad
import Control.Monad.Error
import Utils.Monad.Undo

type IM = TCM
--newtype IM a = IM (TCM a) 

liftTCM :: TCM a -> IM a
liftTCM s = s

--runIM :: IM a -> IO (Either TCErr a)
--runIM (IM m) = runTCM m 


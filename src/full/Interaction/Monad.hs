{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}
module Interaction.Monad where

import TypeChecking.Monad(TCM,runTCM,TCErr)

newtype IM a = IM (TCM a)

liftTCM :: TCM a -> IM a
liftTCM s = IM s

runIM :: IM a -> IO (Either TCErr a)
runIM (IM m) = runTCM m 

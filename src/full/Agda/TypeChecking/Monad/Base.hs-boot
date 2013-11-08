{-# LANGUAGE KindSignatures #-}

module Agda.TypeChecking.Monad.Base where

import Data.IORef (IORef)

data TCEnv
data TCState
newtype TCMT m a = TCM { unTCM :: IORef TCState -> TCEnv -> m a }

type TCM = TCMT IO

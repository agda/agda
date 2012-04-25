{-# LANGUAGE KindSignatures #-}

module Agda.TypeChecking.Monad.Base where

import Control.Monad.Trans

data TCMT (m :: * -> *) a

type TCM = TCMT IO

instance MonadIO m => Monad (TCMT m)

{-# LANGUAGE KindSignatures #-}

module Agda.TypeChecking.Monad.Base where

data TCMT (m :: * -> *) a

type TCM = TCMT IO

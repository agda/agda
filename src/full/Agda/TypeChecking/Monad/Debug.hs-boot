{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Monad.Debug where

import Data.Kind (Type)

class MonadDebug (m :: Type -> Type)

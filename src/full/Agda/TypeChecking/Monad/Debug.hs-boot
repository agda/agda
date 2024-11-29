{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Monad.Debug where

import Agda.TypeChecking.Monad.Base.Types (Capability)
import Data.Kind (Type)

class MonadDebug (m :: Type -> Type)
class CapDebug (c :: Capability)

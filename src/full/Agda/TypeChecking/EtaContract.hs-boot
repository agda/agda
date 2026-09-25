{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.EtaContract where

import Agda.Syntax.Internal.Generic (TermLike)
import {-# SOURCE #-} Agda.TypeChecking.Monad.Signature (HasConstInfo)

etaContract :: (HasConstInfo m, TermLike a) => a -> m a

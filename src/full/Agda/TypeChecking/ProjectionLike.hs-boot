{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.ProjectionLike where

import Agda.Syntax.Abstract.Name (QName)
import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Monad.Signature (HasConstInfo)

makeProjection :: QName -> TCM ()
eligibleForProjectionLike :: (HasConstInfo m) => QName -> m Bool

{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.ProjectionLike where

import {-# SOURCE #-} Agda.TypeChecking.Monad.Pure
import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Monad.Signature (HasConstInfo)
import Agda.Syntax.Internal

makeProjection :: QName -> TCM ()
eligibleForProjectionLike :: (HasConstInfo m) => QName -> m Bool

data ProjEliminator = EvenLone | ButLone | NoPostfix

elimView :: PureTCM m => ProjEliminator -> Term -> m Term

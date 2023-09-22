{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Telescope where

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context (MonadAddContext)
import {-# SOURCE #-} Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Substitute
import Agda.Utils.Empty (Empty)

class PiApplyM a where
  piApplyM' :: (MonadReduce m, HasBuiltins m) => m Empty -> Type -> a -> m Type

  piApplyM :: (MonadReduce m, HasBuiltins m) => Type -> a -> m Type
  piApplyM = piApplyM' __IMPOSSIBLE__

instance PiApplyM Term where
instance PiApplyM a => PiApplyM (Arg a) where
instance PiApplyM a => PiApplyM [a] where

telView :: (MonadReduce m, MonadAddContext m) => Type -> m TelView

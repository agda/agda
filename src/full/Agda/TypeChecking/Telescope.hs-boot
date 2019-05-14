
module Agda.TypeChecking.Telescope where

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context (MonadAddContext)
import Agda.TypeChecking.Substitute

class PiApplyM a where
  piApplyM :: MonadReduce m => Type -> a -> m Type

instance PiApplyM Term where
instance PiApplyM a => PiApplyM (Arg a) where
instance PiApplyM a => PiApplyM [a] where

telView :: (MonadReduce m, MonadAddContext m) => Type -> m TelView

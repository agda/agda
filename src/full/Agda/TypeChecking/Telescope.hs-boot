
module Agda.TypeChecking.Telescope where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Substitute

piApplyM :: MonadReduce m => Type -> Args -> m Type
telView :: Type -> TCM TelView

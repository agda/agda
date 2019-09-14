
module Agda.TypeChecking.Level where

import Control.Monad.Fail (MonadFail)
import Agda.TypeChecking.Monad.Builtin (HasBuiltins)
import Agda.Syntax.Internal

reallyUnLevelView :: (MonadFail m, HasBuiltins m) => Level -> m Term

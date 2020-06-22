
module Agda.TypeChecking.Level where

import Agda.TypeChecking.Monad.Builtin (HasBuiltins)
import Agda.Syntax.Internal

reallyUnLevelView :: (HasBuiltins m) => Level -> m Term

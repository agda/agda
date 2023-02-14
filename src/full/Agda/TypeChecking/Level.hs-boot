
module Agda.TypeChecking.Level where

import Agda.Interaction.Options

import Agda.TypeChecking.Monad.Builtin (HasBuiltins)
import Agda.Syntax.Internal

reallyUnLevelView :: (HasBuiltins m, HasOptions m) => Level -> m Term

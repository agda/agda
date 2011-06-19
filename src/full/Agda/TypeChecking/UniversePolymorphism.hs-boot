
module Agda.TypeChecking.UniversePolymorphism where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

compareLevel :: MonadTCM tcm => Comparison -> Level -> Level -> tcm Constraints

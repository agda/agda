
module Agda.TypeChecking.UniversePolymorphism where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

compareLevel :: MonadTCM tcm => Comparison -> Term -> Term -> tcm Constraints


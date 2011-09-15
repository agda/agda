
module Agda.TypeChecking.UniversePolymorphism where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

compareLevel :: Comparison -> Level -> Level -> TCM ()

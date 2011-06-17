
module Agda.TypeChecking.Level where

import Agda.TypeChecking.Monad
import Agda.Syntax.Internal

unLevelView :: MonadTCM tcm => Level -> tcm Term
levelView :: MonadTCM tcm => Term -> tcm Level

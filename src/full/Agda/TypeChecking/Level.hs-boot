
module Agda.TypeChecking.Level where

import Agda.TypeChecking.Monad
import Agda.Syntax.Internal

newtype LevelView = Max [PlusView]
data PlusView

unLevelView :: MonadTCM tcm => LevelView -> tcm Term
levelView :: MonadTCM tcm => Term -> tcm LevelView



module Agda.TypeChecking.Patterns.Match where

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

data Match = Yes [Term] | No | DontKnow (Maybe MetaId)

matchPatterns :: MonadTCM tcm => [Arg Pattern] -> [Arg Term] -> tcm (Match, [Arg Term])


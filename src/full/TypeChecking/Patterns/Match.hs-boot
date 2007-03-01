
module TypeChecking.Patterns.Match where

import Syntax.Common
import Syntax.Internal
import TypeChecking.Monad

data Match = Yes [Term] | No | DontKnow (Maybe MetaId)

matchPatterns :: MonadTCM tcm => [Arg Pattern] -> [Arg Term] -> [Injective] -> tcm (Match, [Arg Term])


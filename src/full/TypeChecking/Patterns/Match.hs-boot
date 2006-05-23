
module TypeChecking.Patterns.Match where

import Syntax.Common
import Syntax.Internal
import TypeChecking.Monad

data Match = Yes [Term] | No | DontKnow (Maybe MetaId)

matchPatterns :: [Arg Pattern] -> [Arg Term] -> TCM (Match, [Arg Term])


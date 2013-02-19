
module Agda.TypeChecking.Patterns.Match where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

data Match = Yes [Term] | No | DontKnow (Maybe MetaId)

matchPatterns :: [Arg Pattern] -> [Arg Term] -> TCM (Match, [Arg Term])

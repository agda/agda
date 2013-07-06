
module Agda.TypeChecking.Patterns.Match where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

data Match a = Yes Simplification [a] | No | DontKnow (Maybe MetaId)

matchPatterns :: [Arg Pattern] -> [Arg Term] -> TCM (Match Term, [Arg Term])
matchCopatterns :: [Arg Pattern] -> [Elim] -> TCM (Match Elim, [Elim])


module Agda.TypeChecking.Patterns.Match where

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

data Match a = Yes Simplification [a] | No | DontKnow (Blocked ())

matchPatterns   :: [NamedArg Pattern] -> Args  -> ReduceM (Match Term, Args)
matchCopatterns :: [NamedArg Pattern] -> Elims -> ReduceM (Match Term, Elims)

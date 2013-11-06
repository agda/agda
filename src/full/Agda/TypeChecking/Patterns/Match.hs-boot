
module Agda.TypeChecking.Patterns.Match where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

data Match a = Yes Simplification [a] | No | DontKnow (Maybe MetaId)

matchPatterns   :: [NamedArg Pattern] -> Args  -> TCM (Match Term, Args)
matchCopatterns :: [NamedArg Pattern] -> Elims -> TCM (Match Term, Elims)

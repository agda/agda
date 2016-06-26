
module Agda.TypeChecking.Patterns.Match where

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

data Match a = Yes Simplification [Arg a] | No | DontKnow (Blocked ())

matchPatterns   :: [NamedArg DeBruijnPattern] -> Args  -> ReduceM (Match Term, Args)
matchCopatterns :: [NamedArg DeBruijnPattern] -> Elims -> ReduceM (Match Term, Elims)


module Agda.TypeChecking.Patterns.Match where

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import {-# SOURCE #-} Agda.TypeChecking.Pretty (PrettyTCM)

data Match a = Yes Simplification [Arg a] | No | DontKnow (Blocked ())

matchPatterns   :: (Show a) => [NamedArg (Pattern' a)] -> Args  -> ReduceM (Match Term, Args)
matchCopatterns :: (Show a, PrettyTCM a) => [NamedArg (Pattern' a)] -> Elims -> ReduceM (Match Term, Elims)

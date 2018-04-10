
module Agda.TypeChecking.Patterns.Match where

import Data.IntMap (IntMap)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute (DeBruijn)

import Agda.Utils.Empty

data Match a = Yes Simplification (IntMap (Arg a)) | No | DontKnow (Blocked ())

buildSubstitution :: (DeBruijn a) => Empty -> Int -> IntMap (Arg a) -> Substitution' a

matchPatterns   :: [NamedArg DeBruijnPattern] -> Args  -> ReduceM (Match Term, Args)
matchCopatterns :: [NamedArg DeBruijnPattern] -> Elims -> ReduceM (Match Term, Elims)

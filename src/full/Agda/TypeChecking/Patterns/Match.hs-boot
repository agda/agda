{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Patterns.Match where

import Data.IntMap (IntMap)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute (DeBruijn)

import Agda.Utils.Impossible

data Match a = Yes Simplification (IntMap (Arg a)) | No | DontKnow (Blocked ())

buildSubstitution :: (DeBruijn a) => Impossible -> Int -> IntMap (Arg a) -> Substitution' a

type MonadMatch m = PureTCM m

matchPatterns   :: MonadMatch m => [NamedArg DeBruijnPattern] -> Args -> m (Match Term, Args)
matchCopatterns :: MonadMatch m => [NamedArg DeBruijnPattern] -> Elims -> m (Match Term, Elims)

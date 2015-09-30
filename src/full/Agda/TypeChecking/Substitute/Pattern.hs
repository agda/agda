{-# LANGUAGE CPP,
             FlexibleContexts,
             FlexibleInstances,
             MultiParamTypeClasses,
             TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Agda.TypeChecking.Substitute.Pattern where

import Data.Maybe
import Data.Traversable (traverse)

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Substitute

#include "undefined.h"
import Agda.Utils.Impossible

fromPatternSubstitution :: PatternSubstitution -> Substitution
fromPatternSubstitution = fmap patternToTerm

applyPatSubst :: (Subst Term a) => PatternSubstitution -> a -> a
applyPatSubst = applySubst . fromPatternSubstitution

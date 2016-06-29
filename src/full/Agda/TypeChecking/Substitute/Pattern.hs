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

instance DeBruijn DeBruijnPattern where
  debruijnNamedVar n i  = VarP $ DBPatVar n i
  debruijnView (VarP x) = Just $ dbPatVarIndex x
  debruijnView _        = Nothing

fromPatternSubstitution :: PatternSubstitution -> Substitution
fromPatternSubstitution = fmap patternToTerm

applyPatSubst :: (Subst Term a) => PatternSubstitution -> a -> a
applyPatSubst = applySubst . fromPatternSubstitution

instance Subst DeBruijnPattern DeBruijnPattern where
  applySubst IdS p = p
  applySubst rho p = case p of
    VarP x       -> useName (dbPatVarName x) $ lookupS rho $ dbPatVarIndex x
    DotP u       -> DotP $ applyPatSubst rho u
    ConP c ci ps -> ConP c ci $ applySubst rho ps
    LitP x       -> p
    ProjP f      -> p
    where
      useName :: PatVarName -> DeBruijnPattern -> DeBruijnPattern
      useName n (VarP x) | isUnderscore (dbPatVarName x) = debruijnNamedVar n (dbPatVarIndex x)
      useName _ x = x

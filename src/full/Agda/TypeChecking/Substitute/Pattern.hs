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
  debruijnNamedVar n i      = VarP (i,n)
  debruijnView (VarP (i,_)) = Just i
  debruijnView _            = Nothing

fromPatternSubstitution :: PatternSubstitution -> Substitution
fromPatternSubstitution = fmap patternToTerm

applyPatSubst :: (Subst Term a) => PatternSubstitution -> a -> a
applyPatSubst = applySubst . fromPatternSubstitution

instance Subst DeBruijnPattern DeBruijnPattern where
  applySubst IdS p = p
  applySubst rho p = case p of
    VarP (i,n)   -> useName n $ lookupS rho i
    DotP u       -> DotP $ applyPatSubst rho u
    ConP c ci ps -> ConP c ci $ applySubst rho ps
    LitP x       -> p
    ProjP f      -> p
    where
      useName :: PatVarName -> DeBruijnPattern -> DeBruijnPattern
      useName n (VarP (i,"_")) = VarP (i,n)
      useName _ x = x

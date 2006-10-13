{-# OPTIONS -cpp #-}
module TypeChecking.Constraints where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import Control.Applicative
import Data.Map as Map
import Data.List as List

import Syntax.Internal
import TypeChecking.Monad

#ifndef __HADDOCK__
import {-# SOURCE #-} TypeChecking.Conversion
import {-# SOURCE #-} TypeChecking.MetaVars
#endif

import Utils.Fresh

#include "../undefined.h"

-- | Catch pattern violation errors and adds a constraint.
--
catchConstraint :: Constraint -> TCM Constraints -> TCM Constraints
catchConstraint c v =
   catchError v $ \err ->
   case err of
       PatternErr s -> put s >> buildConstraint c
       _	    -> throwError err

-- | We ignore the constraint ids and (as in Agda) retry all constraints every time.
--   We probably generate very few constraints.
wakeupConstraints :: TCM ()
wakeupConstraints = do
    cs <- takeConstraints
    cs <- retryCs cs
    addConstraints cs	-- TODO: there might be a problem of detecting progress
  where
    retryCs :: Constraints -> TCM Constraints
    retryCs cs = concat <$> mapM (withConstraint retry) cs

    retry :: Constraint -> TCM Constraints
    retry (ValueEq a u v)  = equalVal a u v
    retry (TypeEq a b)	   = equalTyp a b
    retry (SortEq s1 s2)   = equalSort s1 s2
    retry (Guarded c cs)   = do
	cs <- retryCs cs
	case cs of
	    []	-> retry c
	    _	-> buildConstraint $ Guarded c cs
    retry (UnBlock m)	   = do
	BlockedConst t <- mvInstantiation <$> lookupMeta m
	setRef m $ InstV t
	return []


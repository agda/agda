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
catchConstraint :: Constraint -> TCM () -> TCM ()
catchConstraint c v =
   catchError v $ \err ->
   case err of
       PatternErr s -> put s >> addConstraint c
       _	    -> throwError err

-- | add a new constraint
--   first arg is a list of @MetaId@s which should wake-up the constraint
--
addConstraint :: Constraint -> TCM ()
addConstraint c =
    do	cl <- buildClosure c
	cId <- fresh
	modify $ \st ->
	    st { stConstraints = Map.insert cId cl $ stConstraints st }

-- | We ignore the constraint ids and (as in Agda) retry all constraints every time.
--   We probably generate very few constraints.
wakeupConstraints :: TCM ()
wakeupConstraints =
    do	cs <- takeConstraints
	mapM_ (withConstraint retry) $ Map.elems cs
  where
    retry (ValueEq a u v)  = equalVal a u v
    retry (TypeEq a b)	   = equalTyp a b
    retry (SortEq s1 s2)   = equalSort s1 s2
    retry (Guarded c [])   = retry c		    -- TODO: need to return new constraints
    retry (Guarded c cs)   = mapM_ retry cs
    retry (UnBlock m)	   = do
	BlockedConst t <- mvInstantiation <$> lookupMeta m
	setRef m $ InstV t


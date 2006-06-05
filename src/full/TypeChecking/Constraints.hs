{-# OPTIONS -cpp #-}
module TypeChecking.Constraints where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import Data.Map as Map
import Data.List as List

import Syntax.Internal
import TypeChecking.Monad

#ifndef __HADDOCK__
import {-# SOURCE #-} TypeChecking.Conversion
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
    do	env <- getEnv
	sig <- getSignature
        scope <- getScope
	cId <- fresh
	modify $ \st -> st { stConstraints = Map.insert cId (CC sig env scope c)
						$ stConstraints st
			   }

-- | We ignore the constraint ids and (as in Agda) retry all constraints every time.
--   We probably generate very few constraints.
wakeupConstraints :: TCM ()
wakeupConstraints =
    do	cs <- takeConstraints
	mapM_ (withConstraint retry) $ Map.elems cs
  where
    retry (ValueEq a u v) = equalVal Why a u v
    retry (TypeEq a b)	  = equalTyp Why a b
    retry (SortLeq s1 s2) = leqSort s1 s2
    retry (SortEq s1 s2)  = equalSort s1 s2


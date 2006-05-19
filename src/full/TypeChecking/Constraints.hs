{-# OPTIONS -cpp #-}
module TypeChecking.Constraints where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import Data.Map as Map
import Data.List as List

import Syntax.Internal
import TypeChecking.Monad
import TypeChecking.Monad.Context

import TypeChecking.Monad.Debug

#ifndef __HADDOCK__
import {-# SOURCE #-} TypeChecking.Conversion
#endif

import Utils.Fresh

#include "../undefined.h"

-- | Catch pattern violation errors and adds a constraint.
--
catchConstr :: Constraint -> TCM () -> TCM ()
catchConstr cnstr v =
   catchError v (\ err -> case err of
       PatternErr mIds -> addCnstr mIds cnstr
       _           -> throwError err
       )

-- | add a new constraint
--   first arg is a list of @MetaId@s which should wake-up the constraint
--
addCnstr :: [MetaId] -> Constraint -> TCM ()
addCnstr mIds c = do
    env <- ask
    sig <- getSignature
    cId <- fresh
    modify (\st -> st{
        stConstraints = Map.insert cId (sig,env,c) $ stConstraints st,
        stMetaStore   = foldr (Map.adjust $ addCId cId) (stMetaStore st) mIds
        })        

-- | We ignore the constraint ids and (as in Agda) retry all constraints every time.
--   We probably generate very few constraints.
wakeupConstraints :: TCM ()
wakeupConstraints =
    do	cs <- takeConstraints
	mapM_ retry $ Map.elems cs
  where
    retry (sig,env,c) =
	withSignature sig
	$ local (const env)
	$ try c

    try (ValueEq a u v) = equalVal Why a u v
    try (TypeEq a b)	= equalTyp Why a b
    try (SortLeq s1 s2)	= leqSort s1 s2
    try (SortEq s1 s2)	= equalSort s1 s2

getCIds (UnderScoreV _ _ cIds) = cIds
getCIds (UnderScoreT _ _ cIds) = cIds
getCIds (UnderScoreS _   cIds) = cIds
getCIds (HoleV       _ _ cIds) = cIds
getCIds (HoleT       _ _ cIds) = cIds
getCIds m		     = error $ "getCIds: " ++ show m -- __IMPOSSIBLE__

addCId cId mInfo = case mInfo of
    UnderScoreV i a cIds -> UnderScoreV i a $ cId : cIds
    UnderScoreT i s cIds -> UnderScoreT i s $ cId : cIds
    UnderScoreS i   cIds -> UnderScoreS i   $ cId : cIds
    HoleV       i a cIds -> HoleV i a       $ cId : cIds
    HoleT       i s cIds -> HoleT i s       $ cId : cIds
    _			 -> __IMPOSSIBLE__


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

-- TODO: remove constraint.
-- Alternative (used in Agda) retry all constraints every time.
-- We probably generate very few constraints.
wakeup cId = do
    cnstrs <- getConstraints
    case Map.lookup cId cnstrs of
        Just (sig, env, ValueEq a m1 m2) -> go sig env $ equalVal Why a m1 m2
        Just (sig, env, TypeEq a1 a2)    -> go sig env $ equalTyp Why a1 a2
	_				 -> __IMPOSSIBLE__
  where
    go sig env v = do
        sigCurrent <- gets stSignature
        modify (\st -> st{stSignature = sig})
        local (const env) v
        modify (\st -> st{stSignature = sigCurrent})

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


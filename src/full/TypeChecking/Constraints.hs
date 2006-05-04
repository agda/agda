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
    ctx <- asks envContext
    sig <- gets stSignature
    cId <- fresh
    modify (\st -> st{
        stConstraints = Map.insert cId (sig,ctx,c) $ stConstraints st,
        stMetaStore   = foldr (Map.adjust $ addCId cId) (stMetaStore st) mIds
        })        

wakeup cId = do
    cnstrs <- gets stConstraints
    case Map.lookup cId cnstrs of
        Just (sig, ctx, ValueEq a m1 m2) -> go sig ctx $ equalVal Why a m1 m2
        Just (sig, ctx, TypeEq a1 a2)    -> go sig ctx $ equalTyp Why a1 a2
	_				 -> __IMPOSSIBLE__
  where
    go sig ctx v = do
        sigCurrent <- gets stSignature
        modify (\st -> st{stSignature = sig})
        local (\e -> e { envContext = ctx }) v
        modify (\st -> st{stSignature = sigCurrent})

getCIds (UnderScoreV _ cIds) = cIds
getCIds (UnderScoreT _ cIds) = cIds
getCIds (UnderScoreS   cIds) = cIds
getCIds (HoleV       _ cIds) = cIds
getCIds (HoleT       _ cIds) = cIds
getCIds m		     = error $ "getCIds: " ++ show m -- __IMPOSSIBLE__

addCId cId mInfo = case mInfo of
    UnderScoreV a cIds -> UnderScoreV a $ cId : cIds
    UnderScoreT s cIds -> UnderScoreT s $ cId : cIds
    UnderScoreS cIds   -> UnderScoreS   $ cId : cIds
    HoleV       a cIds -> HoleV a       $ cId : cIds
    HoleT       s cIds -> HoleT s       $ cId : cIds
    _		       -> __IMPOSSIBLE__


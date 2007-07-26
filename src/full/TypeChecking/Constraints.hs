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
import TypeChecking.Errors
import TypeChecking.Reduce

#ifndef __HADDOCK__
import {-# SOURCE #-} TypeChecking.Rules.Term (checkExpr)
import {-# SOURCE #-} TypeChecking.Conversion
import {-# SOURCE #-} TypeChecking.MetaVars
#endif

import Utils.Fresh

#include "../undefined.h"

-- | Catch pattern violation errors and adds a constraint.
--
catchConstraint :: MonadTCM tcm => Constraint -> TCM Constraints -> tcm Constraints
catchConstraint c v = liftTCM $
   catchError v $ \err ->
   case err of
       PatternErr s -> put s >> buildConstraint c
       _	    -> throwError err

-- | Try to solve the constraints to be added.
addNewConstraints :: MonadTCM tcm => Constraints -> tcm ()
addNewConstraints cs = do addConstraints cs; wakeupConstraints

-- | Don't allow the argument to produce any constraints.
noConstraints :: MonadTCM tcm => tcm Constraints -> tcm ()
noConstraints m = do
    cs <- solveConstraints =<< m
    unless (List.null cs) $ typeError $ UnsolvedConstraints cs
    return ()

-- | Guard constraint
guardConstraint :: MonadTCM tcm => tcm Constraints -> Constraint -> tcm Constraints
guardConstraint m c = do
    cs <- solveConstraints =<< m
    case List.partition isSortConstraint cs of   -- sort constraints doesn't block anything
	(scs, []) -> (scs ++) <$> solveConstraint c
	(scs, cs) -> (scs ++) <$> buildConstraint (Guarded c cs)
    where
	isSortConstraint = isSC . clValue
	isSC (SortEq _ _)    = True
	isSC (ValueEq _ _ _) = False
	isSC (TypeEq _ _)    = False
	isSC (Guarded c _)   = isSC c
	isSC (UnBlock _)     = False

-- | We ignore the constraint ids and (as in Agda) retry all constraints every time.
--   We probably generate very few constraints.
wakeupConstraints :: MonadTCM tcm => tcm ()
wakeupConstraints = do
    cs <- takeConstraints
    cs <- solveConstraints cs
    addConstraints cs

solveConstraints :: MonadTCM tcm => Constraints -> tcm Constraints
solveConstraints cs = do
    n  <- length <$> getInstantiatedMetas
    cs <- concat <$> mapM (withConstraint solveConstraint) cs
    n' <- length <$> getInstantiatedMetas
    if (n' > n)
	then solveConstraints cs -- Go again if we made progress
	else return cs

solveConstraint :: MonadTCM tcm => Constraint -> tcm Constraints
solveConstraint (ValueEq a u v) = equalTerm a u v
solveConstraint (TypeEq a b)	= equalType a b
solveConstraint (SortEq s1 s2)	= equalSort s1 s2
solveConstraint (Guarded c cs)	= guardConstraint (return cs) c
solveConstraint (UnBlock m) = do
    inst <- mvInstantiation <$> lookupMeta m
    case inst of
      BlockedConst t -> do
        verbose 5 $ do
            d <- prettyTCM t
            debug $ show m ++ " := " ++ show d
        assignTerm m t
        return []
      PostponedTypeCheckingProblem e t -> do
        t <- reduce t
        case unEl t of
          MetaV _ _ -> buildConstraint $ UnBlock m
          _         -> do
            v <- liftTCM $ checkExpr e t
            assignTerm m v
            return []
      _ -> __IMPOSSIBLE__


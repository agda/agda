{-# LANGUAGE CPP #-}
module Agda.TypeChecking.Constraints where

import System.IO

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import Control.Applicative
import Data.Map as Map
import Data.List as List
import Data.Set as Set

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce

import {-# SOURCE #-} Agda.TypeChecking.Rules.Term (checkExpr)
import {-# SOURCE #-} Agda.TypeChecking.Conversion
import {-# SOURCE #-} Agda.TypeChecking.MetaVars
import {-# SOURCE #-} Agda.TypeChecking.Empty
import Agda.TypeChecking.Free

import Agda.Utils.Fresh

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Catch pattern violation errors and adds a constraint.
--
catchConstraint :: MonadTCM tcm => Constraint -> TCM Constraints -> tcm Constraints
catchConstraint c v = liftTCM $
   catchError v $ \err ->
   case errError err of
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
    case List.partition isNonBlocking cs of
	(scs, []) -> (scs ++) <$> solveConstraint c
	(scs, cs) -> (scs ++) <$> buildConstraint (Guarded c cs)
    where
	isNonBlocking = isNB . clValue
	isNB SortCmp{}        = True
	isNB ValueCmp{}       = False
	isNB TypeCmp{}        = False
	isNB TelCmp{}         = False
	isNB (Guarded c _)    = isNB c
	isNB UnBlock{}        = False
        isNB IsEmpty{}        = False

-- | We ignore the constraint ids and (as in Agda) retry all constraints every time.
--   We probably generate very few constraints.
wakeupConstraints :: MonadTCM tcm => tcm ()
wakeupConstraints = do
    cs <- takeConstraints
    cs <- solveConstraints cs
    addConstraints cs

solveConstraints :: MonadTCM tcm => Constraints -> tcm Constraints
solveConstraints [] = return []
solveConstraints cs = do
    reportSDoc "tc.constr.solve" 60 $
      sep [ text "{ solving", nest 2 $ prettyTCM cs ]
    n  <- length <$> getInstantiatedMetas
    cs0 <- return cs
    cs <- concat <$> mapM (withConstraint solveConstraint) cs
    n' <- length <$> getInstantiatedMetas
    reportSDoc "tc.constr.solve" 70 $
      sep [ text "new constraints", nest 2 $ prettyTCM cs ]
    cs <- if (n' > n)
	then solveConstraints cs -- Go again if we made progress
	else return cs
    reportSLn "tc.constr.solve" 60 $ "solved constraints }"
    return cs

solveConstraint :: MonadTCM tcm => Constraint -> tcm Constraints
solveConstraint (ValueCmp cmp a u v) = compareTerm cmp a u v
solveConstraint (TypeCmp cmp a b)    = compareType cmp a b
solveConstraint (TelCmp cmp a b)     = compareTel  cmp a b
solveConstraint (SortCmp cmp s1 s2)  = compareSort cmp s1 s2
solveConstraint (Guarded c cs)       = guardConstraint (return cs) c
solveConstraint (IsEmpty t)          = isEmptyTypeC t
solveConstraint (UnBlock m)          = do
    inst <- mvInstantiation <$> lookupMeta m
    reportSDoc "tc.constr.unblock" 15 $ text ("unblocking a metavar yields the constraint: " ++ show inst)
    case inst of
      BlockedConst t -> do
        reportSDoc "tc.constr.blocked" 15 $
          text ("blocked const " ++ show m ++ " :=") <+> prettyTCM t
        assignTerm m t
        return []
      PostponedTypeCheckingProblem cl -> enterClosure cl $ \(e, t, unblock) -> do
        b <- liftTCM unblock
        if not b
          then buildConstraint $ UnBlock m
          else do
            tel <- getContextTelescope
            v   <- liftTCM $ checkExpr e t
            assignTerm m $ teleLam tel v
            return []
      -- Andreas, 2009-02-09, the following were IMPOSSIBLE cases
      -- somehow they pop up in the context of sized types
      --
      -- already solved metavariables: no constraints left (Ulf, is that correct?)
      InstV{} -> return []
      InstS{} -> return []
      -- Open (whatever that means)
      Open -> __IMPOSSIBLE__


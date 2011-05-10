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

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Scope.Base
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

import {-# SOURCE #-} Agda.TypeChecking.Rules.Term (checkExpr)
import {-# SOURCE #-} Agda.TypeChecking.Conversion
import {-# SOURCE #-} Agda.TypeChecking.MetaVars
import {-# SOURCE #-} Agda.TypeChecking.Empty
import {-# SOURCE #-} Agda.TypeChecking.UniversePolymorphism
import Agda.TypeChecking.Free

import Agda.Utils.Fresh
import Agda.Utils.Monad

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Catches pattern violation errors and adds a constraint.
--
catchConstraint :: MonadTCM tcm => Constraint -> TCM Constraints -> tcm Constraints
catchConstraint c v = liftTCM $
   catchError_ v $ \err ->
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

-- | @guardConstraint cs c@ tries to solve constraints @cs@ first.
--   If successful, it moves on to solve @c@, otherwise it returns
--   a @Guarded c cs@.
guardConstraint :: MonadTCM tcm => tcm Constraints -> Constraint -> tcm Constraints
guardConstraint m c = do
    cs <- solveConstraints =<< m
    case List.partition isNonBlocking cs of
	(scs, []) -> (scs ++) <$> solveConstraint c
	(scs, cs) -> (scs ++) <$> buildConstraint (Guarded c cs)
    where
	isNonBlocking = isNB . clValue
	isNB SortCmp{}        = True
        isNB LevelCmp{}       = True
	isNB ValueCmp{}       = False
        isNB ArgsCmp{}        = False
	isNB TypeCmp{}        = False
	isNB TelCmp{}         = False
	isNB (Guarded c _)    = isNB c
	isNB UnBlock{}        = False
	isNB FindInScope{}    = True
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
      sep [ text "new constraints", nest 2 $ prettyTCM cs
          , nest 2 $ text $ "progress: " ++ show n' ++ " --> " ++ show n
          ]
    cs <- if (n' > n)
	then solveConstraints cs -- Go again if we made progress
	else return cs
    reportSLn "tc.constr.solve" 60 $ "solved constraints }"
    return cs

solveConstraint :: MonadTCM tcm => Constraint -> tcm Constraints
solveConstraint (ValueCmp cmp a u v) = compareTerm cmp a u v
solveConstraint (ArgsCmp cmp a u v)  = compareArgs cmp a u v
solveConstraint (TypeCmp cmp a b)    = compareType cmp a b
solveConstraint (TelCmp a b cmp tela telb) = compareTel a b cmp tela telb
solveConstraint (SortCmp cmp s1 s2)  = compareSort cmp s1 s2
solveConstraint (LevelCmp cmp a b)   = compareLevel cmp a b
solveConstraint (Guarded c cs)       = guardConstraint (return cs) c
solveConstraint (IsEmpty t)          = isEmptyTypeC t
solveConstraint (UnBlock m)          =
  ifM (isFrozen m) (buildConstraint $ UnBlock m) $ do
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
      OpenIFS -> __IMPOSSIBLE__
solveConstraint (FindInScope m)      =
  ifM (isFrozen m) (buildConstraint $ FindInScope m) $ do
    reportSDoc "tc.constr.findInScope" 15 $ text ("findInScope constraint: " ++ show m)
    mv <- lookupMeta m
    let j = mvJudgement mv
    case j of
      IsSort{} -> __IMPOSSIBLE__
      HasType _ tj -> do
        ctx <- getContextVars
        ctxArgs <- getContextArgs
        t <- normalise $ tj `piApply` ctxArgs
        reportSLn "tc.constr.findInScope" 15 $ "findInScope t: " ++ show t
        let candsP1 = [(term, t) | (term, t, Instance) <- ctx]
        let candsP2 = [(term, t) | (term, t, h) <- ctx, h /= Instance]
        let scopeInfo = getMetaScope mv
        let ns = everythingInScope scopeInfo
        let nsList = Map.toList $ nsNames ns
        -- try all abstract names in scope (even ones that you can't refer to
        --  unambiguously)
        let candsP3Names = nsList >>= snd
        candsP3Types <- mapM (typeOfConst . anameName) candsP3Names
        candsP3FV <- mapM (freeVarsToApply . anameName) candsP3Names
        let candsP3 = [(Def (anameName an) vs, t) |
                       (an, t, vs) <- zip3 candsP3Names candsP3Types candsP3FV]
        let cands = [candsP1, candsP2, candsP3]
        cands <- mapM (filterM (uncurry $ checkCandidateForMeta m t )) cands
        let iterCands :: MonadTCM tcm => [(Int, [(Term, Type)])] -> tcm Constraints
            iterCands [] = do reportSDoc "tc.constr.findInScope" 15 $ text "not a single candidate found..."
                              typeError $ IFSNoCandidateInScope t
            iterCands ((p, []) : cs) = do reportSDoc "tc.constr.findInScope" 15 $ text $
                                            "no candidates found at p=" ++ show p ++ ", trying next p..."
                                          iterCands cs
            iterCands ((p, [(term, t')]):_) =
              do reportSDoc "tc.constr.findInScope" 15 $ text (
                   "one candidate at p=" ++ show p ++ " found for type '") <+>
                   prettyTCM t <+> text "': '" <+> prettyTCM term <+>
                   text "', of type '" <+> prettyTCM t' <+> text "'."
                 cs <- leqType t t'
                 assignV t m ctxArgs term
                 return cs
            iterCands ((p, cs):_) = do reportSDoc "tc.constr.findInScope" 15 $
                                         text ("still more than one candidate at p=" ++ show p ++ ": ") <+>
                                         prettyTCM (List.map fst cs)
                                       buildConstraint $ FindInScope m
        iterCands [(1,concat cands)]
      where
        getContextVars :: MonadTCM tcm => tcm [(Term, Type, Hiding)]
        getContextVars = do
          ctx <- getContext
          let ids = [0.. fromIntegral (length ctx) - 1] :: [Nat]
          types <- mapM typeOfBV ids
          return $ [ (Var i [], t, h) | (Arg h _ _, i, t) <- zip3 ctx [0..] types ]
        checkCandidateForMeta :: (MonadTCM tcm) => MetaId -> Type -> Term -> Type -> tcm Bool
        checkCandidateForMeta m t term t' =
          liftTCM $ flip catchError (\err -> return False) $ do
            reportSLn "tc.constr.findInScope" 20 $ "checkCandidateForMeta t: " ++ show t ++ "; t':" ++ show t' ++ "; term: " ++ show term ++ "."
            restoreStateTCMT $ do
               -- domi: we assume that nothing below performs direct IO (except
               -- for logging and such, I guess)
               csT <- leqType t t'
               tel <- getContextTelescope
               assignTerm m (teleLam tel term)
               -- make a pass over constraints, to detect cases where some are made
               -- unsolvable by the assignment, but don't do this for FindInScope's
               -- to prevent loops. We currently also ignore UnBlock constraints
               -- to be on the safe side.
               cs <- getTakenConstraints
               solveConstraints (List.filter isSimpleConstraint cs ++ csT)
            return True
        isSimpleConstraint :: ConstraintClosure -> Bool
        isSimpleConstraint (Closure _ _ _ (FindInScope{})) = False
        isSimpleConstraint (Closure _ _ _ (UnBlock{})) = False
        isSimpleConstraint _ = True

restoreStateTCMT :: (Monad m) => TCMT m a -> TCMT m a
restoreStateTCMT (TCM m) = TCM $ \s e -> do (r, s') <- m s e
                                            return (r, s)

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
import Agda.TypeChecking.Irrelevance (unusableRelevance)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.LevelConstraints
import Agda.TypeChecking.MetaVars.Mention

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
catchConstraint :: Constraint -> TCM () -> TCM ()
catchConstraint c v = liftTCM $
   catchError_ v $ \err ->
   case errError err of
        -- Not putting s (which should really be the what's already there) makes things go
        -- a lot slower (+20% total time on standard library). How is that possible??
        -- The problem is most likely that there are internal catchErrors which forgets the
        -- state. catchError should preserve the state on pattern violations.
       PatternErr s -> put s >> addConstraint c
       _	    -> throwError err

addConstraint :: Constraint -> TCM ()
addConstraint c = do
    pids <- asks envActiveProblems
    reportSDoc "tc.constr.add" 20 $ hsep
      [ text "adding constraint"
      , text (show pids)
      , prettyTCM c ]
    -- Need to reduce to reveal possibly blocking metas
    c <- reduce =<< instantiateFull c
    c' <- simpl c
    if (c /= c')
      then do
        reportSDoc "tc.constr.add" 20 $ text "  simplified:" <+> prettyTCM c'
        solveConstraint_ c'
      else addConstraint' c'
  where
    simpl :: Constraint -> TCM Constraint
    simpl c = do
      n <- genericLength <$> getContext
      let isLvl LevelCmp{} = True
          isLvl _          = False
      cs <- getAllConstraints
      lvls <- instantiateFull $ List.filter (isLvl . clValue . theConstraint) cs
      when (not $ List.null lvls) $ reportSDoc "tc.constr.add" 40 $ text "  simplifying using" <+> prettyTCM lvls
      return $ simplifyLevelConstraint n c lvls

-- | Don't allow the argument to produce any constraints.
noConstraints :: TCM a -> TCM a
noConstraints problem = liftTCM $ do
  (pid, x) <- newProblem problem
  cs <- getConstraintsForProblem pid
  unless (List.null cs) $ typeError $ UnsolvedConstraints cs
  return x

-- | Create a fresh problem for the given action.
newProblem :: TCM a -> TCM (ProblemId, a)
newProblem action = do
  pid <- fresh
  -- Don't get distracted by other constraints while working on the problem
  x <- nowSolvingConstraints $ solvingProblem pid action
  -- Now we can check any woken constraints
  solveAwakeConstraints
  return (pid, x)

newProblem_ :: TCM () -> TCM ProblemId
newProblem_ action = fst <$> newProblem action

ifNoConstraints :: TCM a -> (a -> TCM b) -> (ProblemId -> a -> TCM b) -> TCM b
ifNoConstraints check ifNo ifCs = do
  (pid, x) <- newProblem check
  ifM (isProblemSolved pid) (ifNo x) (ifCs pid x)

ifNoConstraints_ :: TCM () -> TCM a -> (ProblemId -> TCM a) -> TCM a
ifNoConstraints_ check ifNo ifCs = ifNoConstraints check (const ifNo) (\pid _ -> ifCs pid)

-- | @guardConstraint cs c@ tries to solve constraints @cs@ first.
--   If successful, it moves on to solve @c@, otherwise it returns
--   a @Guarded c cs@.
guardConstraint :: Constraint -> TCM () -> TCM ()
guardConstraint c blocker =
  ifNoConstraints_ blocker (solveConstraint_ c) (addConstraint . Guarded c)

whenConstraints :: TCM () -> TCM () -> TCM ()
whenConstraints action handler =
  ifNoConstraints_ action (return ()) $ \pid -> do
    stealConstraints pid
    handler

-- | Wake up the constraints depending on the given meta.
wakeupConstraints :: MetaId -> TCM ()
wakeupConstraints x = do
  wakeConstraints (mentionsMeta x)
  solveAwakeConstraints

-- | Wake up all constraints.
wakeupConstraints_ :: TCM ()
wakeupConstraints_ = do
  wakeConstraints (const True)
  solveAwakeConstraints

solveAwakeConstraints :: TCM ()
solveAwakeConstraints = do
    verboseS "profile.constraints" 10 $ liftTCM $ tickMax "max-open-constraints" . genericLength =<< getAllConstraints
    unlessM isSolvingConstraints $ nowSolvingConstraints solve
  where
    solve = do
      reportSDoc "tc.constr.solve" 10 $ hsep [ text "Solving awake constraints."
                                             , text . show . length =<< getAwakeConstraints
                                             , text "remaining." ]
      mc <- takeAwakeConstraint
      flip (maybe $ return ()) mc $ \c -> do
        withConstraint solveConstraint c
        solve

solveConstraint :: Constraint -> TCM ()
solveConstraint c = do
    verboseS "profile.constraints" 10 $ liftTCM $ tick "attempted-constraints"
    verboseBracket "tc.constr.solve" 20 "solving constraint" $ do
      pids <- asks envActiveProblems
      reportSDoc "tc.constr.solve" 20 $ text (show pids) <+> prettyTCM c
      solveConstraint_ c

solveConstraint_ :: Constraint -> TCM ()
solveConstraint_ (ValueCmp cmp a u v)       = compareTerm cmp a u v
solveConstraint_ (ElimCmp cmp a e u v)      = compareElims cmp a e u v
solveConstraint_ (TypeCmp cmp a b)          = compareType cmp a b
solveConstraint_ (TelCmp a b cmp tela telb) = compareTel a b cmp tela telb
solveConstraint_ (SortCmp cmp s1 s2)        = compareSort cmp s1 s2
solveConstraint_ (LevelCmp cmp a b)         = compareLevel cmp a b
solveConstraint_ c0@(Guarded c pid)         = do
  ifM (isProblemSolved pid) (solveConstraint_ c)
                            (addConstraint c0)
solveConstraint_ (IsEmpty t)                = isEmptyType t
solveConstraint_ (UnBlock m)                =
  ifM (isFrozen m) (addConstraint $ UnBlock m) $ do
    inst <- mvInstantiation <$> lookupMeta m
    reportSDoc "tc.constr.unblock" 15 $ text ("unblocking a metavar yields the constraint: " ++ show inst)
    case inst of
      BlockedConst t -> do
        reportSDoc "tc.constr.blocked" 15 $
          text ("blocked const " ++ show m ++ " :=") <+> prettyTCM t
        assignTerm m t
      PostponedTypeCheckingProblem cl -> enterClosure cl $ \(e, t, unblock) -> do
        b <- liftTCM unblock
        if not b
          then addConstraint $ UnBlock m
          else do
            tel <- getContextTelescope
            v   <- liftTCM $ checkExpr e t
            assignTerm m $ teleLam tel v
      -- Andreas, 2009-02-09, the following were IMPOSSIBLE cases
      -- somehow they pop up in the context of sized types
      --
      -- already solved metavariables: should only happen for size
      -- metas (not sure why it does, Andreas?)
      InstV{} -> return ()
      InstS{} -> return ()
      -- Open (whatever that means)
      Open -> __IMPOSSIBLE__
      OpenIFS -> __IMPOSSIBLE__
solveConstraint_ (FindInScope m)      =
  ifM (isFrozen m) (addConstraint $ FindInScope m) $ do
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
        candsP3Types <- mapM (typeOfConst     . anameName) candsP3Names
        candsP3Rel   <- mapM (relOfConst      . anameName) candsP3Names
        candsP3FV    <- mapM (constrFreeVarsToApply . anameName) candsP3Names
        rel          <- asks envRelevance
        let candsP3 = [(Def (anameName an) vs, t) |
                       (an, t, r, vs) <- zip4 candsP3Names candsP3Types candsP3Rel candsP3FV,
                       r `moreRelevant` rel ]
        let cands = [candsP1, candsP2, candsP3]
        cands <- mapM (filterM (uncurry $ checkCandidateForMeta m t )) cands
        let iterCands :: [(Int, [(Term, Type)])] -> TCM ()
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
                 leqType t t'
                 assignV m ctxArgs term
            iterCands ((p, cs):_) = do reportSDoc "tc.constr.findInScope" 15 $
                                         text ("still more than one candidate at p=" ++ show p ++ ": ") <+>
                                         prettyTCM (List.map fst cs)
                                       addConstraint $ FindInScope m
        iterCands [(1,concat cands)]
      where
        constrFreeVarsToApply :: QName -> TCM Args
        constrFreeVarsToApply n = do
          args <- freeVarsToApply n
          defn <- theDef <$> getConstInfo n
          case defn of
            -- drop parameters if it's a projection function...
            Function{ funProjection = Just (rn,i) } -> do
              ci <- theDef <$> getConstInfo rn
              let rpi = case ci of Datatype { dataPars = d } -> d
                                   Record {recPars = d } -> d
                                   Axiom -> toInteger i - 1
                                   _ -> __IMPOSSIBLE__
              let rp = fromInteger rpi
              return $ genericTake (i - rp - 1) args ++ genericDrop (i - 1) args
            _ -> return args
        getContextVars :: TCM [(Term, Type, Hiding)]
        getContextVars = do
          ctx <- getContext
          let ids = [0.. fromIntegral (length ctx) - 1] :: [Nat]
          types <- mapM typeOfBV ids
          let vars = [ (Var i [], t, h) | (Arg h r _, i, t) <- zip3 ctx [0..] types,
                                          not (unusableRelevance r) ]
          -- get let bindings
          env <- asks envLetBindings
          env <- mapM (getOpen . snd) $ Map.toList env
          let lets = [ (v,t,h) | (v, Arg h r t) <- env, not (unusableRelevance r) ]
          return $ vars ++ lets
        checkCandidateForMeta :: MetaId -> Type -> Term -> Type -> TCM Bool
        checkCandidateForMeta m t term t' =
          liftTCM $ flip catchError (\err -> return False) $ do
            reportSLn "tc.constr.findInScope" 20 $ "checkCandidateForMeta\n  t: " ++ show t ++ "\n  t':" ++ show t' ++ "\n  term: " ++ show term ++ "."
            localState $ do
               -- domi: we assume that nothing below performs direct IO (except
               -- for logging and such, I guess)
               leqType t t'
               tel <- getContextTelescope
               assignTerm m (teleLam tel term)
               -- make a pass over constraints, to detect cases where some are made
               -- unsolvable by the assignment, but don't do this for FindInScope's
               -- to prevent loops. We currently also ignore UnBlock constraints
               -- to be on the safe side.
               wakeConstraints (isSimpleConstraint . clValue . theConstraint)
               solveAwakeConstraints
            return True
        isSimpleConstraint :: Constraint -> Bool
        isSimpleConstraint FindInScope{} = False
        isSimpleConstraint UnBlock{}     = False
        isSimpleConstraint _             = True

localState :: MonadState s m => m a -> m a
localState m = do
  s <- get
  x <- m
  put s
  return x

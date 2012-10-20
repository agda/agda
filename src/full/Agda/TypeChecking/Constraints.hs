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
import Agda.Syntax.Position
import Agda.Syntax.Internal
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Scope.Base
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Errors
import Agda.TypeChecking.InstanceArguments
import Agda.TypeChecking.Irrelevance (unusableRelevance)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.LevelConstraints
-- import Agda.TypeChecking.SizedTypes (solveSizeConstraints)
import Agda.TypeChecking.MetaVars.Mention

import {-# SOURCE #-} Agda.TypeChecking.Rules.Term (checkExpr, checkArguments)
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
   case err of
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
    -- the added constraint can cause IFS constraints to be solved
    unless (isIFSConstraint c) $
       wakeConstraints (isIFSConstraint . clValue . theConstraint)
  where
    isIFSConstraint :: Constraint -> Bool
    isIFSConstraint FindInScope{} = True
    isIFSConstraint _ = False
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

-- | @guardConstraint c blocker@ tries to solve @blocker@ first.
--   If successful without constraints, it moves on to solve @c@, otherwise it
--   adds a @Guarded c cs@ constraint
--   to the @blocker@-generated constraints @cs@.
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
  wakeConstraints (const True) -- (mentionsMeta x) -- TODO: needs fixing to cope with shared updates
  solveAwakeConstraints

-- | Wake up all constraints.
wakeupConstraints_ :: TCM ()
wakeupConstraints_ = do
  wakeConstraints (const True)
  solveAwakeConstraints

solveAwakeConstraints :: TCM ()
solveAwakeConstraints = solveAwakeConstraints' False

solveAwakeConstraints' :: Bool -> TCM ()
solveAwakeConstraints' force = do
    verboseS "profile.constraints" 10 $ liftTCM $ tickMax "max-open-constraints" . genericLength =<< getAllConstraints
    whenM ((force ||) . not <$> isSolvingConstraints) $ nowSolvingConstraints $ do
     -- solveSizeConstraints -- Andreas, 2012-09-27 attacks size constrs too early
     solve
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
solveConstraint_ (IsEmpty r t)              = isEmptyType r t
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
solveConstraint_ (FindInScope m cands)      = findInScope m cands

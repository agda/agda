{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Constraints where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.Reader

import qualified Data.List as List
import qualified Data.Set as Set

import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.InstanceArguments
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.LevelConstraints
import Agda.TypeChecking.SizedTypes
import Agda.TypeChecking.Sort
import Agda.TypeChecking.MetaVars.Mention
import Agda.TypeChecking.Warnings

import {-# SOURCE #-} Agda.TypeChecking.Rules.Application
import {-# SOURCE #-} Agda.TypeChecking.Rules.Def
import {-# SOURCE #-} Agda.TypeChecking.Rules.Term
import {-# SOURCE #-} Agda.TypeChecking.Conversion
import {-# SOURCE #-} Agda.TypeChecking.MetaVars
import {-# SOURCE #-} Agda.TypeChecking.Empty

import Agda.Utils.Except ( MonadError(throwError) )
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Lens

#include "undefined.h"
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
       PatternErr{} -> addConstraint c
       _            -> throwError err

addConstraint :: Constraint -> TCM ()
addConstraint c = do
    pids <- asksTC envActiveProblems
    reportSDoc "tc.constr.add" 20 $ hsep
      [ text "adding constraint"
      , text (show $ Set.toList pids)
      , prettyTCM c ]
    -- Need to reduce to reveal possibly blocking metas
    c <- reduce =<< instantiateFull c
    cs <- simpl c
    if ([c] /= cs)
      then do
        reportSDoc "tc.constr.add" 20 $ text "  simplified:" <+> prettyList (map prettyTCM cs)
        mapM_ solveConstraint_ cs
      else mapM_ addConstraint' cs
    -- the added constraint can cause IFS constraints to be solved (but only
    -- the constraints which aren’t blocked on an uninstantiated meta)
    unless (isIFSConstraint c) $
       wakeConstraints (isWakeableIFSConstraint . clValue . theConstraint)
  where
    isWakeableIFSConstraint :: Constraint -> TCM Bool
    isWakeableIFSConstraint (FindInScope _ b _) = caseMaybe b (return True) (\m -> isInstantiatedMeta m)
    isWakeableIFSConstraint _ = return False

    isIFSConstraint :: Constraint -> Bool
    isIFSConstraint FindInScope{} = True
    isIFSConstraint _             = False

    isLvl LevelCmp{} = True
    isLvl _          = False

    -- Try to simplify a level constraint
    simpl :: Constraint -> TCM [Constraint]
    simpl c = if not $ isLvl c then return [c] else do
      cs <- map theConstraint <$> getAllConstraints
      lvls <- instantiateFull $ List.filter (isLvl . clValue) cs
      when (not $ null lvls) $ do
        reportSDoc "tc.constr.lvl" 40 $ text "simplifying level constraint" <+> prettyTCM c
                                        $$ nest 2 (hang (text "using") 2 (prettyTCM lvls))
      return $ simplifyLevelConstraint c $ map clValue lvls

-- | Don't allow the argument to produce any constraints.
noConstraints :: TCM a -> TCM a
noConstraints problem = liftTCM $ do
  (pid, x) <- newProblem problem
  cs <- getConstraintsForProblem pid
  unless (null cs) $ do
    w <- warning_ (UnsolvedConstraints cs)
    typeError $ NonFatalErrors [ w ]
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
  wakeConstraints (return . mentionsMeta x)
  solveAwakeConstraints

-- | Wake up all constraints.
wakeupConstraints_ :: TCM ()
wakeupConstraints_ = do
  wakeConstraints (return . const True)
  solveAwakeConstraints

solveAwakeConstraints :: TCM ()
solveAwakeConstraints = solveAwakeConstraints' False

solveAwakeConstraints' :: Bool -> TCM ()
solveAwakeConstraints' force = do
    verboseS "profile.constraints" 10 $ liftTCM $ tickMax "max-open-constraints" . List.genericLength =<< getAllConstraints
    whenM ((force ||) . not <$> isSolvingConstraints) $ nowSolvingConstraints $ do
     -- solveSizeConstraints -- Andreas, 2012-09-27 attacks size constrs too early
     -- Ulf, 2016-12-06: Don't inherit problems here! Stored constraints
     -- already contain all their dependencies.
     locallyTC eActiveProblems (const Set.empty) solve
  where
    solve = do
      reportSDoc "tc.constr.solve" 10 $ hsep [ text "Solving awake constraints."
                                             , text . show . length =<< getAwakeConstraints
                                             , text "remaining." ]
      whenJustM takeAwakeConstraint $ \ c -> do
        withConstraint solveConstraint c
        solve

solveConstraint :: Constraint -> TCM ()
solveConstraint c = do
    verboseS "profile.constraints" 10 $ liftTCM $ tick "attempted-constraints"
    verboseBracket "tc.constr.solve" 20 "solving constraint" $ do
      pids <- asksTC envActiveProblems
      reportSDoc "tc.constr.solve" 20 $ text (show $ Set.toList pids) <+> prettyTCM c
      solveConstraint_ c

solveConstraint_ :: Constraint -> TCM ()
solveConstraint_ (ValueCmp cmp a u v)       = compareTerm cmp a u v
solveConstraint_ (ValueCmpOnFace cmp p a u v) = compareTermOnFace cmp p a u v
solveConstraint_ (ElimCmp cmp fs a e u v)   = compareElims cmp fs a e u v
solveConstraint_ (TypeCmp cmp a b)          = compareType cmp a b
solveConstraint_ (TelCmp a b cmp tela telb) = compareTel a b cmp tela telb
solveConstraint_ (SortCmp cmp s1 s2)        = compareSort cmp s1 s2
solveConstraint_ (LevelCmp cmp a b)         = compareLevel cmp a b
solveConstraint_ c0@(Guarded c pid)         = do
  ifM (isProblemSolved pid)
    {-then-} (do
      reportSLn "tc.constr.solve" 50 $ "Guarding problem " ++ show pid ++ " is solved, moving on..."
      solveConstraint_ c)
    {-else-} $ do
      reportSLn "tc.constr.solve" 50 $ "Guarding problem " ++ show pid ++ " is still unsolved."
      addConstraint c0
solveConstraint_ (IsEmpty r t)              = isEmptyType r t
solveConstraint_ (CheckSizeLtSat t)         = checkSizeLtSat t
solveConstraint_ (UnBlock m)                =
  ifM (isFrozen m) (addConstraint $ UnBlock m) $ do
    inst <- mvInstantiation <$> lookupMeta m
    reportSDoc "tc.constr.unblock" 15 $ text ("unblocking a metavar yields the constraint: " ++ show inst)
    case inst of
      BlockedConst t -> do
        reportSDoc "tc.constr.blocked" 15 $
          text ("blocked const " ++ prettyShow m ++ " :=") <+> prettyTCM t
        assignTerm m [] t
      PostponedTypeCheckingProblem cl unblock -> enterClosure cl $ \prob -> do
        ifNotM unblock (addConstraint $ UnBlock m) $ do
          tel <- getContextTelescope
          v   <- liftTCM $ checkTypeCheckingProblem prob
          assignTerm m (telToArgs tel) v
      -- Andreas, 2009-02-09, the following were IMPOSSIBLE cases
      -- somehow they pop up in the context of sized types
      --
      -- already solved metavariables: should only happen for size
      -- metas (not sure why it does, Andreas?)
      -- Andreas, 2017-07-11:
      -- I think this is because the size solver instantiates
      -- some metas with infinity but does not clean up the UnBlock constraints.
      -- See also issue #2637.
      -- Ulf, 2018-04-30: The size solver shouldn't touch blocked terms! They have
      -- a twin meta that it's safe to solve.
      InstV{} -> __IMPOSSIBLE__
      -- Open (whatever that means)
      Open -> __IMPOSSIBLE__
      OpenIFS -> __IMPOSSIBLE__
solveConstraint_ (FindInScope m b cands)      = findInScope m cands
solveConstraint_ (CheckFunDef d i q cs)       = checkFunDef d i q cs
solveConstraint_ (HasBiggerSort a)            = hasBiggerSort a
solveConstraint_ (HasPTSRule a b)             = hasPTSRule a b

checkTypeCheckingProblem :: TypeCheckingProblem -> TCM Term
checkTypeCheckingProblem p = case p of
  CheckExpr cmp e t              -> checkExpr' cmp e t
  CheckArgs eh r args t0 t1 k    -> checkArguments eh r args t0 t1 k
  CheckLambda cmp args body target -> checkPostponedLambda cmp args body target
  UnquoteTactic tac hole t       -> unquoteTactic tac hole t $ return hole

debugConstraints :: TCM ()
debugConstraints = verboseS "tc.constr" 50 $ do
  awake    <- useTC stAwakeConstraints
  sleeping <- useTC stSleepingConstraints
  reportSDoc "" 0 $ vcat
    [ text "Current constraints"
    , nest 2 $ vcat [ text "awake " <+> vcat (map prettyTCM awake)
                    , text "asleep" <+> vcat (map prettyTCM sleeping) ] ]

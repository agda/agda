{-# LANGUAGE CPP #-}
module Agda.TypeChecking.Monad.Constraints where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Data.Map as Map
import Data.List as List

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Closure
import Agda.TypeChecking.Monad.Options
import Agda.Utils.Monad
import Agda.Utils.Impossible

#include "../../undefined.h"

-- | Get the current problem
currentProblem :: MonadTCM tcm => tcm ProblemId
currentProblem = asks $ head' . envActiveProblems
  where
    head' []    = {- ' -} __IMPOSSIBLE__
    head' (x:_) = x

-- | Steal all constraints belonging to the given problem and add them to the current problem.
stealConstraints :: MonadTCM tcm => ProblemId -> tcm ()
stealConstraints pid = do
  current <- currentProblem
  reportSLn "tc.constr.steal" 50 $ "problem " ++ show current ++ " is stealing problem " ++ show pid ++ "'s constraints!"
  let rename pc@(PConstr pid' c) | pid' == pid = PConstr current c
                                 | otherwise   = pc
  -- We should never steal from an active problem.
  whenM (elem pid <$> asks envActiveProblems) __IMPOSSIBLE__
  modify $ \s -> s { stAwakeConstraints    = List.map rename $ stAwakeConstraints s
                   , stSleepingConstraints = List.map rename $ stSleepingConstraints s }

solvingProblem :: MonadTCM tcm => ProblemId -> tcm a -> tcm a
solvingProblem pid m = verboseBracket "tc.constr.solve" 50 ("working on problem " ++ show pid) $ do
  x <- local (\e -> e { envActiveProblems = pid : envActiveProblems e }) m
  ifM (isProblemSolved pid) (do
      reportSLn "tc.constr.solve" 50 $ "problem " ++ show pid ++ " was solved!"
      wakeConstraints (blockedOn pid . clValue . theConstraint)
    ) (reportSLn "tc.constr.solve" 50 $ "problem " ++ show pid ++ " was not solved.")
  return x
  where
    blockedOn pid (Guarded _ pid') = pid == pid'
    blockedOn _ _ = False

isProblemSolved :: MonadTCM tcm => ProblemId -> tcm Bool
isProblemSolved pid =
  (&&) <$> (notElem pid <$> asks envActiveProblems)
       <*> (all ((/= pid) . constraintProblem) <$> getAllConstraints)

getConstraintsForProblem :: MonadTCM tcm => ProblemId -> tcm Constraints
getConstraintsForProblem pid = List.filter ((== pid) . constraintProblem) <$> getAllConstraints

-- | Get the awake constraints
getAwakeConstraints :: MonadTCM tcm => tcm Constraints
getAwakeConstraints = gets stAwakeConstraints

wakeConstraints :: MonadTCM tcm => (ProblemConstraint-> Bool) -> tcm ()
wakeConstraints wake = do
  sleepers <- gets stSleepingConstraints
  reportSLn "tc.constr.wake" 50 $ "considering waking sleepers " ++ show (List.map constraintProblem sleepers)
  modify $ \s ->
    let (wakeup, sleepin) = List.partition wake sleepers in
    s { stSleepingConstraints = sleepin
      , stAwakeConstraints    = stAwakeConstraints s ++ wakeup
      }

takeAwakeConstraint :: MonadTCM tcm => tcm (Maybe ProblemConstraint)
takeAwakeConstraint = do
  cs <- getAwakeConstraints
  case cs of
    []     -> return Nothing
    c : cs -> do
      modify $ \s -> s { stAwakeConstraints = cs }
      return (Just c)

getAllConstraints :: MonadTCM tcm => tcm Constraints
getAllConstraints = gets $ \s -> stAwakeConstraints s ++ stSleepingConstraints s

withConstraint :: MonadTCM tcm => (Constraint -> tcm a) -> ProblemConstraint -> tcm a
withConstraint f (PConstr pid c) = do
  -- We should preserve the problem stack
  pids <- asks envActiveProblems
  enterClosure c $ \c ->
    local (\e -> e { envActiveProblems = pids }) $
    solvingProblem pid (f c)

buildProblemConstraint :: MonadTCM tcm => ProblemId -> Constraint -> tcm ProblemConstraint
buildProblemConstraint pid c = PConstr pid <$> buildClosure c

buildConstraint :: MonadTCM tcm => Constraint -> tcm ProblemConstraint
buildConstraint c = flip buildProblemConstraint c =<< currentProblem

-- | Add new a constraint
addConstraint' :: MonadTCM tcm => Constraint -> tcm ()
addConstraint' c = do
    pc <- build
    modify $ \s -> s { stSleepingConstraints = pc : stSleepingConstraints s }
  where
    build | isBlocking c = buildConstraint c
          | otherwise    = buildProblemConstraint 0 c
    isBlocking SortCmp{}     = False
    isBlocking LevelCmp{}    = False
    isBlocking ValueCmp{}    = True
    isBlocking ElimCmp{}     = True
    isBlocking TypeCmp{}     = True
    isBlocking TelCmp{}      = True
    isBlocking (Guarded c _) = isBlocking c
    isBlocking UnBlock{}     = True
    isBlocking FindInScope{} = False
    isBlocking IsEmpty{}     = True

-- | Add already awake constraints
addAwakeConstraints :: MonadTCM tcm => Constraints -> tcm ()
addAwakeConstraints cs = modify $ \s -> s { stAwakeConstraints = cs ++ stAwakeConstraints s }

-- | Start solving constraints
nowSolvingConstraints :: MonadTCM tcm => tcm a -> tcm a
nowSolvingConstraints = local $ \e -> e { envSolvingConstraints = True }

isSolvingConstraints :: MonadTCM tcm => tcm Bool
isSolvingConstraints = asks envSolvingConstraints


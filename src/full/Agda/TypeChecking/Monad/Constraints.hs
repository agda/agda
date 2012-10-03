{-# LANGUAGE CPP #-}
module Agda.TypeChecking.Monad.Constraints where

import Control.Arrow ((&&&))
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
currentProblem :: TCM ProblemId
currentProblem = asks $ head' . envActiveProblems
  where
    head' []    = {- ' -} __IMPOSSIBLE__
    head' (x:_) = x

-- | Steal all constraints belonging to the given problem and add them to the current problem.
stealConstraints :: ProblemId -> TCM ()
stealConstraints pid = do
  current <- currentProblem
  reportSLn "tc.constr.steal" 50 $ "problem " ++ show current ++ " is stealing problem " ++ show pid ++ "'s constraints!"
  let rename pc@(PConstr pid' c) | pid' == pid = PConstr current c
                                 | otherwise   = pc
  -- We should never steal from an active problem.
  whenM (elem pid <$> asks envActiveProblems) __IMPOSSIBLE__
  modify $ \s -> s { stAwakeConstraints    = List.map rename $ stAwakeConstraints s
                   , stSleepingConstraints = List.map rename $ stSleepingConstraints s }

solvingProblem :: ProblemId -> TCM a -> TCM a
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

isProblemSolved :: ProblemId -> TCM Bool
isProblemSolved pid =
  and2M (notElem pid <$> asks envActiveProblems)
        (all ((/= pid) . constraintProblem) <$> getAllConstraints)

getConstraintsForProblem :: ProblemId -> TCM Constraints
getConstraintsForProblem pid = List.filter ((== pid) . constraintProblem) <$> getAllConstraints

-- | Get the awake constraints
getAwakeConstraints :: TCM Constraints
getAwakeConstraints = gets stAwakeConstraints

wakeConstraints :: (ProblemConstraint-> Bool) -> TCM ()
wakeConstraints wake = do
  sleepers <- gets stSleepingConstraints
  let (wakeup, sleepin) = List.partition wake sleepers
  reportSLn "tc.constr.wake" 50 $ "waking up         " ++ show (List.map constraintProblem wakeup) ++ "\n" ++
                                  "  still sleeping: " ++ show (List.map constraintProblem sleepin)
  modify $ \s ->
    s { stSleepingConstraints = sleepin
      , stAwakeConstraints    = stAwakeConstraints s ++ wakeup
      }

-- danger...
dropConstraints :: (ProblemConstraint -> Bool) -> TCM ()
dropConstraints crit = do
  sleepers <- gets stSleepingConstraints
  wakers <- gets stAwakeConstraints
  let filt = List.filter (not . crit)
  modify $ \s -> s { stSleepingConstraints = filt sleepers
                   , stAwakeConstraints = filt wakers
                   }

putAllConstraintsToSleep :: TCM ()
putAllConstraintsToSleep = do
  awakeOnes <- gets stAwakeConstraints
  sleepers <- gets stSleepingConstraints
  modify $ \s -> s { stSleepingConstraints = sleepers ++ awakeOnes
                   , stAwakeConstraints = [] }

takeAwakeConstraint :: TCM (Maybe ProblemConstraint)
takeAwakeConstraint = do
  cs <- getAwakeConstraints
  case cs of
    []     -> return Nothing
    c : cs -> do
      modify $ \s -> s { stAwakeConstraints = cs }
      return (Just c)

getAllConstraints :: TCM Constraints
getAllConstraints = gets $ \s -> stAwakeConstraints s ++ stSleepingConstraints s

withConstraint :: (Constraint -> TCM a) -> ProblemConstraint -> TCM a
withConstraint f (PConstr pid c) = do
  -- We should preserve the problem stack and the isSolvingConstraint flag
  (pids, isSolving) <- asks $ envActiveProblems &&& envSolvingConstraints
  enterClosure c $ \c ->
    local (\e -> e { envActiveProblems = pids, envSolvingConstraints = isSolving }) $
    solvingProblem pid (f c)

buildProblemConstraint :: ProblemId -> Constraint -> TCM ProblemConstraint
buildProblemConstraint pid c = PConstr pid <$> buildClosure c

buildConstraint :: Constraint -> TCM ProblemConstraint
buildConstraint c = flip buildProblemConstraint c =<< currentProblem

-- | Add new a constraint
addConstraint' :: Constraint -> TCM ()
addConstraint' c = do
    pc <- build
    modify $ \s -> s { stDirty = True, stSleepingConstraints = pc : stSleepingConstraints s }
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
addAwakeConstraints :: Constraints -> TCM ()
addAwakeConstraints cs = modify $ \s -> s { stAwakeConstraints = cs ++ stAwakeConstraints s }

-- | Start solving constraints
nowSolvingConstraints :: TCM a -> TCM a
nowSolvingConstraints = local $ \e -> e { envSolvingConstraints = True }

isSolvingConstraints :: TCM Bool
isSolvingConstraints = asks envSolvingConstraints


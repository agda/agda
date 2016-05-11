{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Constraints where

import Control.Arrow ((&&&))
import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader

import Data.List as List

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Closure
import Agda.TypeChecking.Monad.Options

import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Monad

#include "undefined.h"
import Agda.Utils.Impossible

-- | Get the current problem
currentProblem :: TCM ProblemId
currentProblem = headWithDefault __IMPOSSIBLE__ <$> asks envActiveProblems

-- | Steal all constraints belonging to the given problem and add them to the current problem.
stealConstraints :: ProblemId -> TCM ()
stealConstraints pid = do
  current <- currentProblem
  reportSLn "tc.constr.steal" 50 $ "problem " ++ show current ++ " is stealing problem " ++ show pid ++ "'s constraints!"
  -- Rename @pid@ to @current@ in all constraints.
  let rename pc@(PConstr pid' c) | pid' == pid = PConstr current c
                                 | otherwise   = pc
  -- We should never steal from an active problem.
  whenM (elem pid <$> asks envActiveProblems) __IMPOSSIBLE__
  modifyAwakeConstraints    $ List.map rename
  modifySleepingConstraints $ List.map rename

solvingProblem :: ProblemId -> TCM a -> TCM a
solvingProblem pid m = verboseBracket "tc.constr.solve" 50 ("working on problem " ++ show pid) $ do
  x <- local (\e -> e { envActiveProblems = pid : envActiveProblems e }) m
  ifNotM (isProblemSolved pid)
    (reportSLn "tc.constr.solve" 50 $ "problem " ++ show pid ++ " was not solved.")
    $ {- else -} do
      reportSLn "tc.constr.solve" 50 $ "problem " ++ show pid ++ " was solved!"
      wakeConstraints (return . blockedOn pid . clValue . theConstraint)
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
getAwakeConstraints = use stAwakeConstraints

wakeConstraints :: (ProblemConstraint-> TCM Bool) -> TCM ()
wakeConstraints wake = do
  c <- use stSleepingConstraints
  (wakeup, sleepin) <- partitionM wake c
  reportSLn "tc.constr.wake" 50 $
    "waking up         " ++ show (List.map constraintProblem wakeup) ++ "\n" ++
    "  still sleeping: " ++ show (List.map constraintProblem sleepin)
  modifySleepingConstraints $ const sleepin
  modifyAwakeConstraints (++ wakeup)

-- danger...
dropConstraints :: (ProblemConstraint -> Bool) -> TCM ()
dropConstraints crit = do
  let filt = List.filter $ not . crit
  modifySleepingConstraints filt
  modifyAwakeConstraints    filt

putAllConstraintsToSleep :: TCM ()
putAllConstraintsToSleep = do
  awakeOnes <- use stAwakeConstraints
  modifySleepingConstraints $ (++ awakeOnes)
  modifyAwakeConstraints    $ const []

takeAwakeConstraint :: TCM (Maybe ProblemConstraint)
takeAwakeConstraint = do
  cs <- getAwakeConstraints
  case cs of
    []     -> return Nothing
    c : cs -> do
      modifyAwakeConstraints $ const cs
      return $ Just c

getAllConstraints :: TCM Constraints
getAllConstraints = gets $ \s -> s^.stAwakeConstraints ++ s^.stSleepingConstraints

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
    stDirty .= True
    stSleepingConstraints %= (pc :)
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
    isBlocking CheckSizeLtSat{} = True

-- | Add already awake constraints
addAwakeConstraints :: Constraints -> TCM ()
addAwakeConstraints cs = modifyAwakeConstraints (cs ++)

-- | Start solving constraints
nowSolvingConstraints :: TCM a -> TCM a
nowSolvingConstraints = local $ \e -> e { envSolvingConstraints = True }

isSolvingConstraints :: TCM Bool
isSolvingConstraints = asks envSolvingConstraints

---------------------------------------------------------------------------
-- * Lenses
---------------------------------------------------------------------------

mapAwakeConstraints :: (Constraints -> Constraints) -> TCState -> TCState
mapAwakeConstraints = over stAwakeConstraints

mapSleepingConstraints :: (Constraints -> Constraints) -> TCState -> TCState
mapSleepingConstraints = over stSleepingConstraints

modifyAwakeConstraints  :: (Constraints -> Constraints) -> TCM ()
modifyAwakeConstraints = modify . mapAwakeConstraints

modifySleepingConstraints  :: (Constraints -> Constraints) -> TCM ()
modifySleepingConstraints = modify . mapSleepingConstraints

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
import Agda.Utils.Except

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
  let rename pc@(PConstr pids c) | elem pid pids = PConstr (current : pids) c
                                 | otherwise     = pc
  -- We should never steal from an active problem.
  whenM (elem pid <$> asks envActiveProblems) __IMPOSSIBLE__
  modifyAwakeConstraints    $ List.map rename
  modifySleepingConstraints $ List.map rename

solvingProblem :: ProblemId -> TCM a -> TCM a
solvingProblem pid = solvingProblems [pid]

solvingProblems :: [ProblemId] -> TCM a -> TCM a
solvingProblems pids m = verboseBracket "tc.constr.solve" 50 ("working on problems " ++ show pids) $ do
  x <- local (\e -> e { envActiveProblems = pids ++ envActiveProblems e }) m
  sequence_
    [ ifNotM (isProblemSolved pid)
        (reportSLn "tc.constr.solve" 50 $ "problem " ++ show pid ++ " was not solved.")
      $ {- else -} do
        reportSLn "tc.constr.solve" 50 $ "problem " ++ show pid ++ " was solved!"
        wakeConstraints (return . blockedOn pid . clValue . theConstraint)
    | pid <- pids ]
  return x
  where
    blockedOn pid (Guarded _ pid') = pid == pid'
    blockedOn _ _ = False

isProblemSolved :: ProblemId -> TCM Bool
isProblemSolved pid =
  and2M (notElem pid <$> asks envActiveProblems)
        (all (notElem pid . constraintProblems) <$> getAllConstraints)

getConstraintsForProblem :: ProblemId -> TCM Constraints
getConstraintsForProblem pid = List.filter (elem pid . constraintProblems) <$> getAllConstraints

-- | Get the awake constraints
getAwakeConstraints :: TCM Constraints
getAwakeConstraints = use stAwakeConstraints

wakeConstraints :: (ProblemConstraint-> TCM Bool) -> TCM ()
wakeConstraints wake = do
  c <- use stSleepingConstraints
  (wakeup, sleepin) <- partitionM wake c
  reportSLn "tc.constr.wake" 50 $
    "waking up         " ++ show (List.map constraintProblems wakeup) ++ "\n" ++
    "  still sleeping: " ++ show (List.map constraintProblems sleepin)
  modifySleepingConstraints $ const sleepin
  modifyAwakeConstraints (++ wakeup)

-- danger...
dropConstraints :: (ProblemConstraint -> Bool) -> TCM ()
dropConstraints crit = do
  let filt = List.filter $ not . crit
  modifySleepingConstraints filt
  modifyAwakeConstraints    filt

putConstraintsToSleep :: (ProblemConstraint -> Bool) -> TCM ()
putConstraintsToSleep sleepy = do
  awakeOnes <- use stAwakeConstraints
  let (gotoSleep, stayAwake) = partition sleepy awakeOnes
  modifySleepingConstraints $ (++ gotoSleep)
  modifyAwakeConstraints    $ const stayAwake

putAllConstraintsToSleep :: TCM ()
putAllConstraintsToSleep = putConstraintsToSleep (const True)

data ConstraintStatus = AwakeConstraint | SleepingConstraint
  deriving (Eq, Show)

-- | Suspend constraints matching the predicate during the execution of the
--   second argument. Caution: held sleeping constraints will not be woken up
--   by events that would normally trigger a wakeup call.
holdConstraints :: (ConstraintStatus -> ProblemConstraint -> Bool) -> TCM a -> TCM a
holdConstraints p m = do
  (holdAwake, stillAwake)   <- partition (p AwakeConstraint)    <$> use stAwakeConstraints
  (holdAsleep, stillAsleep) <- partition (p SleepingConstraint) <$> use stSleepingConstraints
  stAwakeConstraints    .= stillAwake
  stSleepingConstraints .= stillAsleep
  let restore = do
        stAwakeConstraints    %= (holdAwake ++)
        stSleepingConstraints %= (holdAsleep ++)
  catchError (m <* restore) (\ err -> restore *> throwError err)

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
withConstraint f (PConstr pids c) = do
  -- We should preserve the problem stack and the isSolvingConstraint flag
  (pids', isSolving) <- asks $ envActiveProblems &&& envSolvingConstraints
  enterClosure c $ \c ->
    local (\e -> e { envActiveProblems = pids', envSolvingConstraints = isSolving }) $
    solvingProblems pids (f c)

buildProblemConstraint :: [ProblemId] -> Constraint -> TCM ProblemConstraint
buildProblemConstraint pids c = PConstr pids <$> buildClosure c

buildProblemConstraint_ :: Constraint -> TCM ProblemConstraint
buildProblemConstraint_ = buildProblemConstraint []

buildConstraint :: Constraint -> TCM ProblemConstraint
buildConstraint c = flip buildProblemConstraint c . nub . filter (> 0) =<< asks envActiveProblems

-- | Add new a constraint
addConstraint' :: Constraint -> TCM ()
addConstraint' c = do
    pc <- build
    stDirty .= True
    stSleepingConstraints %= (pc :)
  where
    build | isBlocking c = buildConstraint c
          | otherwise    = buildProblemConstraint_ c
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

{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Constraints where

import Control.Arrow ((&&&))
import Control.Monad.State
import Control.Monad.Reader

import qualified Data.Foldable as Fold
import qualified Data.List as List
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Closure
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Options

import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Except

#include "undefined.h"
import Agda.Utils.Impossible

-- | Add all constraints belonging to the given problem to the current problem(s).
stealConstraints :: ProblemId -> TCM ()
stealConstraints pid = do
  current <- asksTC envActiveProblems
  reportSLn "tc.constr.steal" 50 $ "problem " ++ show (Set.toList current) ++ " is stealing problem " ++ show pid ++ "'s constraints!"
  -- Add current to any constraint in pid.
  let rename pc@(PConstr pids c) | Set.member pid pids = PConstr (Set.union current pids) c
                                 | otherwise           = pc
  -- We should never steal from an active problem.
  whenM (Set.member pid <$> asksTC envActiveProblems) __IMPOSSIBLE__
  modifyAwakeConstraints    $ List.map rename
  modifySleepingConstraints $ List.map rename

solvingProblem :: ProblemId -> TCM a -> TCM a
solvingProblem pid = solvingProblems (Set.singleton pid)

solvingProblems :: Set ProblemId -> TCM a -> TCM a
solvingProblems pids m = verboseBracket "tc.constr.solve" 50 ("working on problems " ++ show (Set.toList pids)) $ do
  x <- localTC (\e -> e { envActiveProblems = pids `Set.union` envActiveProblems e }) m
  Fold.forM_ pids $ \ pid -> do
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
  and2M (not . Set.member pid <$> asksTC envActiveProblems)
        (all (not . Set.member pid . constraintProblems) <$> getAllConstraints)

getConstraintsForProblem :: ProblemId -> TCM Constraints
getConstraintsForProblem pid = List.filter (Set.member pid . constraintProblems) <$> getAllConstraints

-- | Get the awake constraints
getAwakeConstraints :: TCM Constraints
getAwakeConstraints = useTC stAwakeConstraints

wakeConstraints :: (ProblemConstraint-> TCM Bool) -> TCM ()
wakeConstraints wake = do
  c <- useTC stSleepingConstraints
  (wakeup, sleepin) <- partitionM wake c
  reportSLn "tc.constr.wake" 50 $
    "waking up         " ++ show (List.map (Set.toList . constraintProblems) wakeup) ++ "\n" ++
    "  still sleeping: " ++ show (List.map (Set.toList . constraintProblems) sleepin)
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
  awakeOnes <- useTC stAwakeConstraints
  let (gotoSleep, stayAwake) = List.partition sleepy awakeOnes
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
  (holdAwake, stillAwake)   <- List.partition (p AwakeConstraint)    <$> useTC stAwakeConstraints
  (holdAsleep, stillAsleep) <- List.partition (p SleepingConstraint) <$> useTC stSleepingConstraints
  stAwakeConstraints    `setTCLens` stillAwake
  stSleepingConstraints `setTCLens` stillAsleep
  let restore = do
        stAwakeConstraints    `modifyTCLens` (holdAwake ++)
        stSleepingConstraints `modifyTCLens` (holdAsleep ++)
  catchError (m <* restore) (\ err -> restore *> throwError err)

takeAwakeConstraint :: TCM (Maybe ProblemConstraint)
takeAwakeConstraint = takeAwakeConstraint' (const True)

takeAwakeConstraint' :: (ProblemConstraint -> Bool) -> TCM (Maybe ProblemConstraint)
takeAwakeConstraint' p = do
  cs <- getAwakeConstraints
  case break p cs of
    (_, [])       -> return Nothing
    (cs0, c : cs) -> do
      modifyAwakeConstraints $ const (cs0 ++ cs)
      return $ Just c

getAllConstraints :: TCM Constraints
getAllConstraints = getsTC $ \s -> s^.stAwakeConstraints ++ s^.stSleepingConstraints

withConstraint :: (Constraint -> TCM a) -> ProblemConstraint -> TCM a
withConstraint f (PConstr pids c) = do
  -- We should preserve the problem stack and the isSolvingConstraint flag
  (pids', isSolving) <- asksTC $ envActiveProblems &&& envSolvingConstraints
  enterClosure c $ \c ->
    localTC (\e -> e { envActiveProblems = pids', envSolvingConstraints = isSolving }) $
    solvingProblems pids (f c)

buildProblemConstraint :: Set ProblemId -> Constraint -> TCM ProblemConstraint
buildProblemConstraint pids c = PConstr pids <$> buildClosure c

buildProblemConstraint_ :: Constraint -> TCM ProblemConstraint
buildProblemConstraint_ = buildProblemConstraint Set.empty

buildConstraint :: Constraint -> TCM ProblemConstraint
buildConstraint c = flip buildProblemConstraint c =<< asksTC envActiveProblems

-- | Add new a constraint
addConstraint' :: Constraint -> TCM ()
addConstraint' = addConstraintTo stSleepingConstraints

addAwakeConstraint' :: Constraint -> TCM ()
addAwakeConstraint' = addConstraintTo stAwakeConstraints

addConstraintTo :: Lens' Constraints TCState -> Constraint -> TCM ()
addConstraintTo bucket c = do
    pc <- build
    stDirty `setTCLens` True
    bucket `modifyTCLens` (pc :)
  where
    build | isBlocking c = buildConstraint c
          | otherwise    = buildProblemConstraint_ c
    isBlocking SortCmp{}     = False
    isBlocking LevelCmp{}    = False
    isBlocking ValueCmp{}    = True
    isBlocking ValueCmpOnFace{} = True
    isBlocking ElimCmp{}     = True
    isBlocking TypeCmp{}     = True
    isBlocking TelCmp{}      = True
    isBlocking (Guarded c _) = isBlocking c
    isBlocking UnBlock{}     = True
    isBlocking FindInstance{} = False
    isBlocking IsEmpty{}     = True
    isBlocking CheckSizeLtSat{} = True
    isBlocking CheckFunDef{} = True
    isBlocking HasBiggerSort{} = False
    isBlocking HasPTSRule{}  = False
    isBlocking UnquoteTactic{} = True

-- | Add already awake constraints
addAwakeConstraints :: Constraints -> TCM ()
addAwakeConstraints cs = modifyAwakeConstraints (cs ++)

-- | Start solving constraints
nowSolvingConstraints :: TCM a -> TCM a
nowSolvingConstraints = localTC $ \e -> e { envSolvingConstraints = True }

isSolvingConstraints :: TCM Bool
isSolvingConstraints = asksTC envSolvingConstraints

---------------------------------------------------------------------------
-- * Lenses
---------------------------------------------------------------------------

mapAwakeConstraints :: (Constraints -> Constraints) -> TCState -> TCState
mapAwakeConstraints = over stAwakeConstraints

mapSleepingConstraints :: (Constraints -> Constraints) -> TCState -> TCState
mapSleepingConstraints = over stSleepingConstraints

modifyAwakeConstraints  :: (Constraints -> Constraints) -> TCM ()
modifyAwakeConstraints = modifyTC . mapAwakeConstraints

modifySleepingConstraints  :: (Constraints -> Constraints) -> TCM ()
modifySleepingConstraints = modifyTC . mapSleepingConstraints

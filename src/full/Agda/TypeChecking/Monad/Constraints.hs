
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

import Agda.Utils.Impossible

solvingProblem :: MonadConstraint m => ProblemId -> m a -> m a
solvingProblem pid = solvingProblems (Set.singleton pid)

solvingProblems :: MonadConstraint m => Set ProblemId -> m a -> m a
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

isProblemSolved :: (MonadTCEnv m, ReadTCState m) => ProblemId -> m Bool
isProblemSolved pid =
  and2M (not . Set.member pid <$> asksTC envActiveProblems)
        (all (not . Set.member pid . constraintProblems) <$> getAllConstraints)

getConstraintsForProblem :: ReadTCState m => ProblemId -> m Constraints
getConstraintsForProblem pid = List.filter (Set.member pid . constraintProblems) <$> getAllConstraints

-- | Get the awake constraints
getAwakeConstraints :: ReadTCState m => m Constraints
getAwakeConstraints = useR stAwakeConstraints

-- danger...
dropConstraints :: MonadConstraint m => (ProblemConstraint -> Bool) -> m ()
dropConstraints crit = do
  let filt = List.filter $ not . crit
  modifySleepingConstraints filt
  modifyAwakeConstraints    filt

putConstraintsToSleep :: MonadConstraint m => (ProblemConstraint -> Bool) -> m ()
putConstraintsToSleep sleepy = do
  awakeOnes <- useR stAwakeConstraints
  let (gotoSleep, stayAwake) = List.partition sleepy awakeOnes
  modifySleepingConstraints $ (++ gotoSleep)
  modifyAwakeConstraints    $ const stayAwake

putAllConstraintsToSleep :: MonadConstraint m => m ()
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

takeAwakeConstraint :: MonadConstraint m => m (Maybe ProblemConstraint)
takeAwakeConstraint = takeAwakeConstraint' (const True)

takeAwakeConstraint'
  :: MonadConstraint m
  => (ProblemConstraint -> Bool) -> m (Maybe ProblemConstraint)
takeAwakeConstraint' p = do
  cs <- getAwakeConstraints
  case break p cs of
    (_, [])       -> return Nothing
    (cs0, c : cs) -> do
      modifyAwakeConstraints $ const (cs0 ++ cs)
      return $ Just c

getAllConstraints :: ReadTCState m => m Constraints
getAllConstraints = do
  s <- getTCState
  return $ s^.stAwakeConstraints ++ s^.stSleepingConstraints

withConstraint :: MonadConstraint m => (Constraint -> m a) -> ProblemConstraint -> m a
withConstraint f (PConstr pids c) = do
  -- We should preserve the problem stack and the isSolvingConstraint flag
  (pids', isSolving) <- asksTC $ envActiveProblems &&& envSolvingConstraints
  enterClosure c $ \c ->
    localTC (\e -> e { envActiveProblems = pids', envSolvingConstraints = isSolving }) $
    solvingProblems pids (f c)

buildProblemConstraint
  :: (MonadTCEnv m, ReadTCState m)
  => Set ProblemId -> Constraint -> m ProblemConstraint
buildProblemConstraint pids c = PConstr pids <$> buildClosure c

buildProblemConstraint_
  :: (MonadTCEnv m, ReadTCState m)
  => Constraint -> m ProblemConstraint
buildProblemConstraint_ = buildProblemConstraint Set.empty

buildConstraint :: Constraint -> TCM ProblemConstraint
buildConstraint c = flip buildProblemConstraint c =<< asksTC envActiveProblems

-- | Monad service class containing methods for adding and solving
--   constraints
class ( MonadTCEnv m
      , ReadTCState m
      , MonadError TCErr m
      , HasOptions m
      , MonadDebug m
      ) => MonadConstraint m where
  -- | Unconditionally add the constraint.
  addConstraint :: Constraint -> m ()

  -- | Add constraint as awake constraint.
  addAwakeConstraint :: Constraint -> m ()

  -- | `catchPatternErr handle m` runs m, handling pattern violations
  --    with `handle` (doesn't roll back the state)
  catchPatternErr :: m a -> m a -> m a

  solveConstraint :: Constraint -> m ()

  -- | Solve awake constraints matching the predicate. If the second argument is
  --   True solve constraints even if already 'isSolvingConstraints'.
  solveSomeAwakeConstraints :: (ProblemConstraint -> Bool) -> Bool -> m ()

  wakeConstraints :: (ProblemConstraint-> m Bool) -> m ()

  stealConstraints :: ProblemId -> m ()

  modifyAwakeConstraints :: (Constraints -> Constraints) -> m ()

  modifySleepingConstraints  :: (Constraints -> Constraints) -> m ()

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

-- | Start solving constraints
nowSolvingConstraints :: MonadTCEnv m => m a -> m a
nowSolvingConstraints = localTC $ \e -> e { envSolvingConstraints = True }

isSolvingConstraints :: MonadTCEnv m => m Bool
isSolvingConstraints = asksTC envSolvingConstraints

-- | Add constraint if the action raises a pattern violation
catchConstraint :: MonadConstraint m => Constraint -> m () -> m ()
catchConstraint c = catchPatternErr $ addConstraint c

---------------------------------------------------------------------------
-- * Lenses
---------------------------------------------------------------------------

mapAwakeConstraints :: (Constraints -> Constraints) -> TCState -> TCState
mapAwakeConstraints = over stAwakeConstraints

mapSleepingConstraints :: (Constraints -> Constraints) -> TCState -> TCState
mapSleepingConstraints = over stSleepingConstraints

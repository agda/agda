
module Agda.TypeChecking.Monad.Constraints where

import Control.Monad.Except
import Control.Monad.Reader

import qualified Data.Foldable as Fold
import qualified Data.List as List
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Interaction.Options.Base
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Closure
import Agda.TypeChecking.Monad.Debug

import Agda.Utils.List
import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.Tuple ((&&&))
import Agda.Utils.StrictReader qualified as Strict

{-# INLINE solvingProblem #-}
solvingProblem :: MonadConstraint m => ProblemId -> m a -> m a
solvingProblem pid m = verboseBracket "tc.constr.solve" 50 ("working on problem " ++ show pid) $ do
  x <- localTC (over eActiveProblems (Set.insert pid)) m
  ifNotM (isProblemSolved pid)
      (reportSLn "tc.constr.solve" 50 $ "problem " ++ show pid ++ " was not solved.")
    $ {- else -} do
      reportSLn "tc.constr.solve" 50 $ "problem " ++ show pid ++ " was solved!"
      wakeConstraints (wakeIfBlockedOnProblem pid . constraintUnblocker)
  return x

{-# INLINE solvingProblems #-}
solvingProblems :: MonadConstraint m => Set ProblemId -> m a -> m a
solvingProblems pids m = verboseBracket "tc.constr.solve" 50 ("working on problems " ++ show (Set.toList pids)) $ do
  x <- localTC (over eActiveProblems (pids `Set.union`)) m
  Fold.forM_ pids \pid -> do
    ifNotM (isProblemSolved pid)
        (reportSLn "tc.constr.solve" 50 $ "problem " ++ show pid ++ " was not solved.")
      $ {- else -} do
        reportSLn "tc.constr.solve" 50 $ "problem " ++ show pid ++ " was solved!"
        wakeConstraints (wakeIfBlockedOnProblem pid . constraintUnblocker)
  return x

isProblemSolved :: (MonadTCEnv m, ReadTCState m) => ProblemId -> m Bool
isProblemSolved = isProblemSolved' False

isProblemCompletelySolved :: (MonadTCEnv m, ReadTCState m) => ProblemId -> m Bool
isProblemCompletelySolved = isProblemSolved' True

isProblemSolved' :: (MonadTCEnv m, ReadTCState m) => Bool -> ProblemId -> m Bool
isProblemSolved' completely pid = do
  active <- viewTC eActiveProblems
  tc     <- getTCState
  pure $!    not (Set.member pid active)
          && not (any belongsToUs (tc ^. stAwakeConstraints))
          && not (any belongsToUs (tc ^. stSleepingConstraints))
  where
    belongsToUs c
      | Set.notMember pid (constraintProblems c)         = False
      | isBlockingConstraint (clValue $ theConstraint c) = True
      | otherwise                                        = completely -- Ignore non-blocking unless `completely`

isProblemSolved'' :: ProblemId -> TCM Bool
isProblemSolved'' pid = do
  active <- viewTC eActiveProblems
  tc     <- getTCState
  pure $!    not (any belongsToUs (tc ^. stAwakeConstraints))
          && not (any belongsToUs (tc ^. stSleepingConstraints))
  where
    belongsToUs c
      | Set.notMember pid (constraintProblems c)         = False
      | isBlockingConstraint (clValue $ theConstraint c) = True
      | otherwise                                        = False

{-# SPECIALIZE getConstraintsForProblem :: ProblemId -> TCM Constraints #-}
getConstraintsForProblem :: ReadTCState m => ProblemId -> m Constraints
getConstraintsForProblem pid = filter' (Set.member pid . constraintProblems) <$> getAllConstraints

-- | Get the awake constraints
getAwakeConstraints :: ReadTCState m => m Constraints
getAwakeConstraints = useR stAwakeConstraints

-- danger...
dropConstraints :: MonadConstraint m => (ProblemConstraint -> Bool) -> m ()
dropConstraints crit = do
  let filt = filter' $ not . crit
  modifyConstraints filt filt

-- | Takes out all constraints matching given filter.
--   Danger!  The taken constraints need to be solved or put back at some point.
takeConstraints :: MonadConstraint m => (ProblemConstraint -> Bool) -> m Constraints
takeConstraints f = do
  tc <- getTCState
  let (takeAwake , keepAwake ) = partition' f $ tc ^. stAwakeConstraints
  let (takeAsleep, keepAsleep) = partition' f $ tc ^. stSleepingConstraints
  modifyConstraints (const keepAwake) (const keepAsleep)
  return $! takeAwake ++! takeAsleep

putConstraintsToSleep :: MonadConstraint m => (ProblemConstraint -> Bool) -> m ()
putConstraintsToSleep sleepy = do
  awakeOnes <- useR stAwakeConstraints
  let (!gotoSleep, !stayAwake) = partition' sleepy awakeOnes
  modifyConstraints (const stayAwake) (++! gotoSleep) -- TODO: quadratic append!

putAllConstraintsToSleep :: MonadConstraint m => m ()
putAllConstraintsToSleep = putConstraintsToSleep (const True)

data ConstraintStatus = AwakeConstraint | SleepingConstraint
  deriving (Eq, Show)

-- | Suspend constraints matching the predicate during the execution of the
--   second argument. Caution: held sleeping constraints will not be woken up
--   by events that would normally trigger a wakeup call.
holdConstraints :: (ConstraintStatus -> ProblemConstraint -> Bool) -> TCM a -> TCM a
holdConstraints p m = do
  tc <- getTCState
  let (!holdAwake,  !stillAwake)  = partition' (p AwakeConstraint)    $ tc ^. stAwakeConstraints
  let (!holdAsleep, !stillAsleep) = partition' (p SleepingConstraint) $ tc ^. stSleepingConstraints
  modifyTC' $ set stAwakeConstraints stillAwake . set stSleepingConstraints stillAsleep
  let restore = modifyTC' $ over stAwakeConstraints (holdAwake ++!)
                          . over stSleepingConstraints (holdAsleep ++!)
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
      modifyAwakeConstraints $ const (cs0 ++! cs)
      return $ Just c

getAllConstraints :: ReadTCState m => m Constraints
getAllConstraints = do
  s <- getTCState
  return $! s ^. stAwakeConstraints ++! s ^. stSleepingConstraints

withConstraint :: MonadConstraint m => (Constraint -> m a) -> ProblemConstraint -> m a
withConstraint f (PConstr pids _ c) = do
  -- We should preserve the problem stack and the isSolvingConstraint flag
  pids'     <- viewTC eActiveProblems
  isSolving <- viewTC eSolvingConstraints
  enterClosure c \c ->
    localTC (set eActiveProblems pids' . set eSolvingConstraints isSolving) $
      solvingProblems pids (f c)

buildProblemConstraint
  :: (MonadTCEnv m, ReadTCState m)
  => Set ProblemId -> Blocker -> Constraint -> m ProblemConstraint
buildProblemConstraint pids unblock c = PConstr pids unblock <$> buildClosure c

buildProblemConstraint_
  :: (MonadTCEnv m, ReadTCState m)
  => Blocker -> Constraint -> m ProblemConstraint
buildProblemConstraint_ = buildProblemConstraint Set.empty

buildConstraint :: Blocker -> Constraint -> TCM ProblemConstraint
buildConstraint unblock c = do
  pids <- viewTC eActiveProblems
  buildProblemConstraint pids unblock c

-- | Monad service class containing methods for adding and solving
--   constraints
class ( MonadTCEnv m
      , ReadTCState m
      , MonadError TCErr m
      , MonadBlock m
      , HasOptions m
      , MonadDebug m
      ) => MonadConstraint m where
  -- | Unconditionally add the constraint.
  addConstraint :: Blocker -> Constraint -> m ()

  -- | Add constraint as awake constraint.
  addAwakeConstraint :: Blocker -> Constraint -> m ()

  solveConstraint :: Constraint -> m ()

  -- | Solve awake constraints matching the predicate. If the second argument is
  --   True solve constraints even if already 'isSolvingConstraints'.
  solveSomeAwakeConstraints :: (ProblemConstraint -> Bool) -> Bool -> m ()

  wakeConstraints :: (ProblemConstraint-> WakeUp) -> m ()

  stealConstraints :: ProblemId -> m ()

  -- | Modify both awake (first argument) and sleeping (second argument) constraints.
  modifyConstraints :: (Constraints -> Constraints) -> (Constraints -> Constraints) -> m ()

  {-# INLINE modifyAwakeConstraints #-}
  modifyAwakeConstraints :: (Constraints -> Constraints) -> m ()
  modifyAwakeConstraints f = modifyConstraints f id

  {-# INLINE modifySleepingConstraints #-}
  modifySleepingConstraints  :: (Constraints -> Constraints) -> m ()
  modifySleepingConstraints f = modifyConstraints id f

instance MonadConstraint m => MonadConstraint (ReaderT e m) where
  addConstraint             = (lift .) . addConstraint
  addAwakeConstraint        = (lift .) . addAwakeConstraint
  solveConstraint           = lift . solveConstraint
  solveSomeAwakeConstraints = (lift .) . solveSomeAwakeConstraints
  stealConstraints          = lift . stealConstraints
  modifyConstraints         = (lift .) . modifyConstraints
  wakeConstraints           = lift . wakeConstraints

instance MonadConstraint m => MonadConstraint (Strict.ReaderT e m) where
  {-# INLINE addConstraint #-}
  addConstraint             = (lift .) . addConstraint
  {-# INLINE addAwakeConstraint #-}
  addAwakeConstraint        = (lift .) . addAwakeConstraint
  {-# INLINE solveConstraint #-}
  solveConstraint           = lift . solveConstraint
  {-# INLINE solveSomeAwakeConstraints #-}
  solveSomeAwakeConstraints = (lift .) . solveSomeAwakeConstraints
  {-# INLINE stealConstraints #-}
  stealConstraints          = lift . stealConstraints
  {-# INLINE modifyConstraints #-}
  modifyConstraints         = (lift .) . modifyConstraints
  {-# INLINE wakeConstraints #-}
  wakeConstraints           = lift . wakeConstraints

-- | Add new a constraint
addConstraint' :: Blocker -> Constraint -> TCM ()
addConstraint' = addConstraintTo stSleepingConstraints

addAwakeConstraint' :: Blocker -> Constraint -> TCM ()
addAwakeConstraint' = addConstraintTo stAwakeConstraints

{-# INLINE addConstraintTo #-}
addConstraintTo :: Lens' TCState Constraints -> Blocker -> Constraint -> TCM ()
addConstraintTo bucket unblock c = do
    pc <- buildConstraint unblock c
    tc <- getTCState
    putTC $! tc & stDirty .~ True & bucket %~ (pc :)

-- | A problem is considered solved if there are no unsolved blocking constraints belonging to it.
--   There's no really good principle for what constraints are blocking and which are not, but the
--   general idea is that nothing bad should happen if you assume a non-blocking constraint is
--   solvable, but it turns out it isn't. For instance, assuming an equality constraint between two
--   types that turns out to be false can lead to ill typed terms in places where we don't expect
--   them.
isBlockingConstraint :: Constraint -> Bool
isBlockingConstraint = \case
  SortCmp{}             -> False
  LevelCmp{}            -> False
  FindInstance{}        -> False
  ResolveInstanceHead{} -> False
  HasBiggerSort{}       -> False
  HasPTSRule{}          -> False
  CheckDataSort{}       -> False
  ValueCmp{}            -> True
  ValueCmpOnFace{}      -> True
  ElimCmp{}             -> True
  UnBlock{}             -> True
  IsEmpty{}             -> True
  CheckSizeLtSat{}      -> True
  CheckFunDef{}         -> True
  UnquoteTactic{}       -> True
  CheckMetaInst{}       -> True
  CheckType{}           -> True
  CheckLockedVars{}     -> True
  UsableAtModality{}    -> True
  RewConstraint{}       -> True

-- | Start solving constraints
nowSolvingConstraints :: MonadTCEnv m => m a -> m a
nowSolvingConstraints = localTC (set eSolvingConstraints True)

isSolvingConstraints :: MonadTCEnv m => m Bool
isSolvingConstraints = viewTC eSolvingConstraints

{-# INLINE catchConstraint #-}
-- | Add constraint if the action raises a pattern violation
catchConstraint :: MonadConstraint m => Constraint -> m () -> m ()
catchConstraint c = catchPatternErr \unblock -> addConstraint unblock c

isInstanceConstraint :: Constraint -> Bool
isInstanceConstraint FindInstance{} = True
isInstanceConstraint _              = False

canDropRecursiveInstance :: (ReadTCState m, HasOptions m) => m Bool
canDropRecursiveInstance =
  and2M ((^. stConsideringInstance) <$> getTCState)
        (not . optBacktrackingInstances <$> pragmaOptions)

shouldPostponeInstanceSearch :: (ReadTCState m, HasOptions m) => m Bool
shouldPostponeInstanceSearch = canDropRecursiveInstance `or2M` ((^. stPostponeInstanceSearch) <$> getTCState)

-- | Wake constraints matching the given predicate (and aren't instance
--   constraints if 'shouldPostponeInstanceSearch').
wakeConstraints' :: MonadConstraint m => (ProblemConstraint -> WakeUp) -> m ()
wakeConstraints' p = do
  skipInstance <- shouldPostponeInstanceSearch
  let skip c = skipInstance && isInstanceConstraint (clValue $ theConstraint c)
  wakeConstraints $ wakeUpWhen (not . skip) p

---------------------------------------------------------------------------
-- * Lenses
---------------------------------------------------------------------------

mapAwakeConstraints :: (Constraints -> Constraints) -> TCState -> TCState
mapAwakeConstraints = over stAwakeConstraints

mapSleepingConstraints :: (Constraints -> Constraints) -> TCState -> TCState
mapSleepingConstraints = over stSleepingConstraints


module Agda.TypeChecking.Monad.Constraints where

import Control.Arrow ((&&&))
import Control.Monad.Except
import Control.Monad.Reader

import qualified Data.Foldable as Fold
import qualified Data.List as List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Semigroup ((<>))

import Agda.Interaction.Options.Base
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Closure
import Agda.TypeChecking.Monad.Debug
import {-# SOURCE #-} Agda.TypeChecking.Monad.MetaVars

import Agda.Utils.Maybe
import Agda.Utils.Lens
import Agda.Utils.Monad

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
        wakeConstraints (wakeIfBlockedOnProblem pid . constraintUnblocker)
  return x

isProblemSolved :: (MonadTCEnv m, ReadTCState m) => ProblemId -> m Bool
isProblemSolved pid =
  and2M (not . Set.member pid <$> asksTC envActiveProblems)
        (not . any (Set.member pid . constraintProblems) <$> getAllConstraints)

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

-- | Takes out all constraints matching given filter.
--   Danger!  The taken constraints need to be solved or put back at some point.
takeConstraints :: MonadConstraint m => (ProblemConstraint -> Bool) -> m Constraints
takeConstraints f = do
  (takeAwake , keepAwake ) <- List.partition f <$> useTC stAwakeConstraints
  (takeAsleep, keepAsleep) <- List.partition f <$> useTC stSleepingConstraints
  modifyAwakeConstraints    $ const keepAwake
  modifySleepingConstraints $ const keepAsleep
  return $ takeAwake ++ takeAsleep

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

isBlockedOnIP :: ReadTCState m => Blocker -> m Bool
isBlockedOnIP (UnblockOnAll m)  = allM (Set.toList m) isBlockedOnIP
isBlockedOnIP (UnblockOnAny m)  = anyM (Set.toList m) isBlockedOnIP
isBlockedOnIP (UnblockOnMeta m) = isJust <$> isInteractionMeta m
isBlockedOnIP (UnblockOnProblem i) =
  flip anyM (isBlockedOnIP . constraintUnblocker) =<< getConstraintsForProblem i

isBlockedOnIP UnblockOnDef{}     = pure False

getAllConstraints :: ReadTCState m => m Constraints
getAllConstraints = do
  s <- getTCState
  return $ s^.stAwakeConstraints ++ s^.stSleepingConstraints

withConstraint :: MonadConstraint m => (Constraint -> m a) -> ProblemConstraint -> m a
withConstraint f (PConstr pids _ c) = do
  -- We should preserve the problem stack and the isSolvingConstraint flag
  (pids', isSolving) <- asksTC $ envActiveProblems &&& envSolvingConstraints
  enterClosure c $ \c ->
    localTC (\e -> e { envActiveProblems = pids', envSolvingConstraints = isSolving }) $
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
  pids <- asksTC envActiveProblems
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

  modifyAwakeConstraints :: (Constraints -> Constraints) -> m ()

  modifySleepingConstraints  :: (Constraints -> Constraints) -> m ()

instance MonadConstraint m => MonadConstraint (ReaderT e m) where
  addConstraint             = (lift .) . addConstraint
  addAwakeConstraint        = (lift .) . addAwakeConstraint
  solveConstraint           = lift . solveConstraint
  solveSomeAwakeConstraints = (lift .) . solveSomeAwakeConstraints
  stealConstraints          = lift . stealConstraints
  modifyAwakeConstraints    = lift . modifyAwakeConstraints
  modifySleepingConstraints = lift . modifySleepingConstraints
  wakeConstraints = lift . wakeConstraints

-- | Add new a constraint
addConstraint' :: Blocker -> Constraint -> TCM ()
addConstraint' = addConstraintTo stSleepingConstraints

addAwakeConstraint' :: Blocker -> Constraint -> TCM ()
addAwakeConstraint' = addConstraintTo stAwakeConstraints

addConstraintTo :: Lens' Constraints TCState -> Blocker -> Constraint -> TCM ()
addConstraintTo bucket unblock c = do
    pc <- build
    stDirty `setTCLens` True
    bucket `modifyTCLens` (pc :)
  where
    build | isBlocking c = buildConstraint unblock c
          | otherwise    = buildProblemConstraint_ unblock c
    isBlocking = \case
      SortCmp{}        -> False
      LevelCmp{}       -> False
      FindInstance{}   -> False
      HasBiggerSort{}  -> False
      HasPTSRule{}     -> False
      CheckDataSort{}  -> False
      ValueCmp{}       -> True
      ValueCmpOnFace{} -> True
      ElimCmp{}        -> True
      UnBlock{}        -> True
      IsEmpty{}        -> True
      CheckSizeLtSat{} -> True
      CheckFunDef{}    -> True
      UnquoteTactic{}  -> True
      CheckMetaInst{}  -> True
      CheckType{}      -> True
      CheckLockedVars{} -> True
      UsableAtModality{} -> True

-- | Start solving constraints
nowSolvingConstraints :: MonadTCEnv m => m a -> m a
nowSolvingConstraints = localTC $ \e -> e { envSolvingConstraints = True }

isSolvingConstraints :: MonadTCEnv m => m Bool
isSolvingConstraints = asksTC envSolvingConstraints

-- | Add constraint if the action raises a pattern violation
catchConstraint :: MonadConstraint m => Constraint -> m () -> m ()
catchConstraint c = catchPatternErr $ \ unblock -> addConstraint unblock c

isInstanceConstraint :: Constraint -> Bool
isInstanceConstraint FindInstance{} = True
isInstanceConstraint _              = False

shouldPostponeInstanceSearch :: (ReadTCState m, HasOptions m) => m Bool
shouldPostponeInstanceSearch =
  and2M ((^. stConsideringInstance) <$> getTCState)
        (not . optOverlappingInstances <$> pragmaOptions)
  `or2M` ((^. stPostponeInstanceSearch) <$> getTCState)

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

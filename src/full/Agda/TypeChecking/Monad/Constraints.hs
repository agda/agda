{-# LANGUAGE CPP                        #-}
{-# LANGUAGE TypeOperators              #-}

module Agda.TypeChecking.Monad.Constraints where

import Control.Arrow ((&&&))
import Control.Monad.Except
import Control.Monad.Reader

import qualified Data.Foldable as Fold
import qualified Data.List as List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Semigroup ((<>))
import Data.Bifunctor (bimap)

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Closure
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Heterogeneous
import Agda.TypeChecking.Substitute.Class (Subst)

import Agda.Utils.Lens
import Agda.Utils.Monad

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
        wakeConstraints (wakeIfBlockedOnProblem pid . constraintUnblocker)
  return x

isProblemSolved :: (MonadTCEnv m, ReadTCState m) => ProblemId -> m Bool
isProblemSolved pid =
  and2M (not . Set.member pid <$> asksTC envActiveProblems)
        (not . any (Set.member pid . constraintProblems) <$> getAllConstraints)

getConstraintsForProblem :: ReadTCState m => ProblemId -> m Constraints
getConstraintsForProblem pid = List.filter (Set.member pid . constraintProblems) <$> getAllConstraints

-- | Warning : These constraints need to be solved or put back somehow
takeAsleepConstraints :: MonadConstraint m => (ProblemConstraint -> Bool) -> m Constraints
takeAsleepConstraints f = do
  (takeAsleep, keepAsleep) <- List.partition f <$> useTC stSleepingConstraints
  modifySleepingConstraints $ const keepAsleep
  return $ takeAsleep

putBackAwakeConstraints :: MonadConstraint m => Constraints -> m ()
putBackAwakeConstraints awake = modifyAwakeConstraints (++ awake)

putBackAsleepConstraints :: MonadConstraint m => Constraints -> m ()
putBackAsleepConstraints asleep = modifyAwakeConstraints (++ asleep)

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

  wakeConstraints :: (ProblemConstraint -> WakeUp) -> m ()

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

addAndUnblocker :: MonadBlock m => Blocker -> m a -> m a
addAndUnblocker u
  | u == alwaysUnblock = id
  | otherwise          = catchPatternErr $ \ u' -> patternViolation (u <> u')

addOrUnblocker :: MonadBlock m => Blocker -> m a -> m a
addOrUnblocker u
  | u == neverUnblock = id
  | otherwise         = catchPatternErr $ \ u' -> patternViolation (unblockOnEither u u')

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
      ValueCmp{}       -> True
      ValueCmp_{}      -> True
      ValueCmpOnFace{} -> True
      ElimCmp{}        -> True
      ElimCmp_{}       -> True
      UnBlock{}        -> True
      IsEmpty{}        -> True
      CheckSizeLtSat{} -> True
      CheckFunDef{}    -> True
      UnquoteTactic{}  -> True
      CheckMetaInst{}  -> True
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

---------------------------------------------------------------------------
-- * Lenses
---------------------------------------------------------------------------

mapAwakeConstraints :: (Constraints -> Constraints) -> TCState -> TCState
mapAwakeConstraints = over stAwakeConstraints

mapSleepingConstraints :: (Constraints -> Constraints) -> TCState -> TCState
mapSleepingConstraints = over stSleepingConstraints

---------------------------------------------------------------------------
-- * Twins
---------------------------------------------------------------------------

type SimplifyHetM m = (MonadTCEnv m, ReadTCState m, MonadAddContext m)

class AsTwin a => IsTwinSolved a where
  blockOnTwin ::  (SimplifyHetM m) => a -> m Blocker
  isTwinSolved :: (SimplifyHetM m) => a -> m Bool
  simplifyHet' :: (SimplifyHetM m) => a -> (Either a (AsTwin_ a) -> m b) -> m b

  default simplifyHet' :: (SimplifyHetM m, TwinAt 'Compat a, AsTwin_ a ~ TwinAt_ 'Compat a) =>
                          a -> (Either a (AsTwin_ a) -> m b) -> m b
  simplifyHet' b κ = isTwinSolved b >>= \case
    False -> κ (Left b)
    True  -> κ (Right (twinAt @'Compat b))

instance IsTwinSolved (TwinT' a) where
  blockOnTwin SingleT{}      = return AlwaysUnblock
  blockOnTwin TwinT{twinPid} =
    unblockOnAll . Set.fromList . map UnblockOnProblem <$> filterM (fmap not . isProblemSolved) twinPid

  isTwinSolved SingleT{}      = return True
  isTwinSolved TwinT{twinPid} = allM twinPid isProblemSolved

instance IsTwinSolved a => IsTwinSolved (Dom a) where
  blockOnTwin = blockOnTwin . unDom
  isTwinSolved = isTwinSolved . unDom
  simplifyHet' dom κ = simplifyHet' (unDom dom) $ \a ->
    κ (bimap (\x -> dom{unDom=x}) (\x -> dom{unDom=x}) a)

instance IsTwinSolved a => IsTwinSolved (CompareAs' a) where
  blockOnTwin (AsTermsOf a) = blockOnTwin a
  blockOnTwin AsTypes       = return AlwaysUnblock
  blockOnTwin AsSizes       = return AlwaysUnblock

  isTwinSolved (AsTermsOf a) = isTwinSolved a
  isTwinSolved AsTypes       = return True
  isTwinSolved AsSizes       = return True

  simplifyHet' (AsTermsOf a) κ = simplifyHet' a $ \a -> κ (bimap AsTermsOf AsTermsOf a)
  simplifyHet' AsTypes       κ = κ (Right AsTypes)
  simplifyHet' AsSizes       κ = κ (Right AsSizes)

instance IsTwinSolved Name where
  blockOnTwin _  = pure AlwaysUnblock
  isTwinSolved _ = pure True
  simplifyHet' n κ = κ (Right n)

instance (IsTwinSolved a, IsTwinSolved b) => IsTwinSolved (a,b) where
  blockOnTwin  (a,b) = unblockOnBoth <$> blockOnTwin a <*> blockOnTwin b
  isTwinSolved (a,b) = andM [isTwinSolved b, isTwinSolved a]
  simplifyHet' (a,b) κ =
    simplifyHet' a $ \a ->
      simplifyHet' b $ \b ->
        case (a,b) of
          (Right a, Right b) -> κ$ Right (a, b)
          ( Left a, Right b) -> κ$ Left  (a, asTwin b)
          (Right a,  Left b) -> κ$ Left  (asTwin a, b)
          ( Left a,  Left b) -> κ$ Left  (a, b)

instance IsTwinSolved () where
  blockOnTwin ()  = pure AlwaysUnblock
  isTwinSolved () = pure True
  simplifyHet' () κ = κ (Right ())

instance (IsTwinSolved a, IsTwinSolved b) => IsTwinSolved (a :∈ b) where
  blockOnTwin  (b :∋ a) = unblockOnBoth <$> blockOnTwin b <*> blockOnTwin a
  isTwinSolved (b :∋ a) = andM [isTwinSolved b, isTwinSolved a]
  simplifyHet' (b :∋ a) κ = simplifyHet' b $ \case
    Right b -> simplifyHet' a $ \case
      Right a -> κ (Right (a :∈ b))
      Left  a -> κ (Left  (a :∈ asTwin b))
    Left  b -> κ (Left (a :∈ b))

instance (IsTwinSolved a, Subst a) => IsTwinSolved (Abs a) where
  blockOnTwin = blockOnTwin . unAbs
  isTwinSolved = isTwinSolved . unAbs
  simplifyHet' abs κ =
    κ =<< (underAbstraction_ abs $ \a ->
      simplifyHet' a $ \a ->
        return $ bimap (\x -> abs{unAbs=x}) (\x -> abs{unAbs=x}) a)

type SimplifyHet a = (IsTwinSolved a)

-- TODO: One could also check free variables and strengthen the
-- context, but this is supposed to be a cheap operation
simplifyHet :: forall a c m. (SimplifyHetM m, SimplifyHet a) => a -> (a -> m c) -> m c
simplifyHet b κ = go Empty =<< getContext_
  where
    go acc Empty =
      unsafeModifyContext {- IdS -} (const acc) $ simplifyHet' b $ \case
                  Left  b -> κ b
                  Right b -> κ (asTwin b)
    go acc ctx@(a :⊢: γΓ)  =
      simplifyHet' a $ \case
        Right a' -> go (acc :⊢ (asTwin a')) γΓ
        Left  _  -> unsafeModifyContext {- IdS -} (const (acc ⊢:: ctx)) $ κ b

-- | Remove unnecessary twins from the context
simplifyContextHet :: SimplifyHetM m => m a -> m a
simplifyContextHet m = simplifyHet () (\() -> m)

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Agda.TypeChecking.Conversion.Pure where

import Control.Monad.Fail (MonadFail)
import Control.Monad.State

import Data.String

import Agda.Syntax.Common
import Agda.Syntax.Internal

import {-# SOURCE #-} Agda.TypeChecking.Conversion
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Warnings

import Agda.Utils.Either
import Agda.Utils.Except
import Agda.Utils.Null

import Agda.Utils.Impossible

data FreshThings = FreshThings
  { freshInt       :: Int
  , freshProblemId :: ProblemId
  , freshNameId    :: NameId
  }

newtype PureConversionT m a = PureConversionT
  { unPureConversionT :: ExceptT TCErr (StateT FreshThings m) a }
  deriving (Functor, Applicative, Monad, MonadError TCErr, MonadState FreshThings)

pureEqualTerm
  :: (MonadReduce m, MonadAddContext m, HasBuiltins m, HasConstInfo m)
  => Type -> Term -> Term -> m Bool
pureEqualTerm a u v = locallyTC eCompareBlocked (const True) $
  isRight <$> runPureConversion (equalTerm a u v)

pureCompareAs
  :: (MonadReduce m, MonadAddContext m, HasBuiltins m, HasConstInfo m)
  => Comparison -> CompareAs -> Term -> Term -> m Bool
pureCompareAs cmp a u v = locallyTC eCompareBlocked (const True) $
  isRight <$> runPureConversion (compareAs cmp a u v)

runPureConversion
  :: (ReadTCState m, MonadDebug m, HasOptions m, MonadTCEnv m, Show a)
  => PureConversionT m a -> m (Either TCErr a)
runPureConversion (PureConversionT m) = do
  i <- useR stFreshInt
  pid <- useR stFreshProblemId
  nid <- useR stFreshNameId
  let frsh = FreshThings i pid nid
  result <- fst <$> runStateT (runExceptT m) frsh
  reportSLn "tc.conv.pure" 40 $ "runPureConversion result: " ++ show result
  return result

deriving instance MonadFail       m => MonadFail       (PureConversionT m)
deriving instance HasBuiltins     m => HasBuiltins     (PureConversionT m)
deriving instance HasConstInfo    m => HasConstInfo    (PureConversionT m)
deriving instance HasOptions      m => HasOptions      (PureConversionT m)
deriving instance MonadTCEnv      m => MonadTCEnv      (PureConversionT m)
deriving instance ReadTCState     m => ReadTCState     (PureConversionT m)
deriving instance MonadReduce     m => MonadReduce     (PureConversionT m)
deriving instance MonadAddContext m => MonadAddContext (PureConversionT m)
deriving instance MonadDebug      m => MonadDebug      (PureConversionT m)

instance (Monad m, Semigroup a) => Semigroup (PureConversionT m a) where
  d1 <> d2 = (<>) <$> d1 <*> d2

instance (IsString a, Monad m) => IsString (PureConversionT m a) where
  fromString s = return (fromString s)

instance Monad m => Null (PureConversionT m Doc) where
  empty = return empty
  null = __IMPOSSIBLE__

instance (MonadTCEnv m, ReadTCState m, HasOptions m, MonadDebug m)
  => MonadConstraint (PureConversionT m) where
  addConstraint c = patternViolation
  addAwakeConstraint c = patternViolation
  catchPatternErr handle m = m `catchError` \case
    PatternErr{} -> handle
    err          -> throwError err
  solveConstraint c = patternViolation
  solveSomeAwakeConstraints _ _ = return ()
  wakeConstraints _ = return ()
  stealConstraints _ = return ()
  modifyAwakeConstraints _ = patternViolation
  modifySleepingConstraints _ = patternViolation

instance (MonadTCEnv m, MonadReduce m, MonadAddContext m, ReadTCState m, HasBuiltins m, HasConstInfo m, MonadDebug m)
  => MonadMetaSolver (PureConversionT m) where
  newMeta' _ _ _ _ _ _ = patternViolation
  assignV _ _ _ _ _ = patternViolation
  assignTerm' _ _ _ = patternViolation
  etaExpandMeta _ _ = return ()
  updateMetaVar _ _ = patternViolation
  speculateMetas fallback m = m >>= \case
    KeepMetas     -> return ()
    RollBackMetas -> fallback

instance (MonadTCEnv m, ReadTCState m) => MonadInteractionPoints (PureConversionT m) where
  freshInteractionId = patternViolation
  modifyInteractionPoints _ = patternViolation

-- This is a bogus instance that promptly forgets all concrete names,
-- but we don't really care
instance ReadTCState m => MonadStConcreteNames (PureConversionT m) where
  runStConcreteNames m = do
    concNames <- useR stConcreteNames
    fst <$> runStateT m concNames

instance (MonadReduce m, MonadAddContext m, HasConstInfo m, HasBuiltins m)
  => MonadWarning (PureConversionT m) where
  addWarning w = case classifyWarning (tcWarning w) of
    ErrorWarnings -> patternViolation
    AllWarnings   -> return ()

instance ReadTCState m => MonadStatistics (PureConversionT m) where
  modifyCounter _ _ = return ()

instance Monad m => MonadFresh ProblemId (PureConversionT m) where
  fresh = do
    i <- gets freshProblemId
    modify $ \f -> f { freshProblemId = i + 1 }
    return i

instance Monad m => MonadFresh NameId (PureConversionT m) where
  fresh = do
    i <- gets freshNameId
    modify $ \f -> f { freshNameId = succ i }
    return i

instance Monad m => MonadFresh Int (PureConversionT m) where
  fresh = do
    i <- gets freshInt
    modify $ \f -> f { freshInt = i + 1 }
    return i

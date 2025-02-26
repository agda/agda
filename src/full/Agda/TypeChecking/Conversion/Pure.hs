
module Agda.TypeChecking.Conversion.Pure where

import Control.Monad.Except
import Control.Monad.State

import Data.String

import Agda.Syntax.Common
import Agda.Syntax.Internal

import {-# SOURCE #-} Agda.TypeChecking.Conversion
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce (isBlocked)
import Agda.TypeChecking.Warnings

import Agda.Utils.Maybe
import Agda.Utils.Null

import Agda.Utils.Impossible

data FreshThings = FreshThings
  { freshInt       :: Int
  , freshProblemId :: ProblemId
  , freshNameId    :: NameId
  }

newtype PureConversionT m a = PureConversionT
  { unPureConversionT :: ExceptT TCErr (StateT FreshThings m) a }
  deriving (Functor, Applicative, Monad, MonadError TCErr, MonadState FreshThings, PureTCM)

{-# SPECIALIZE pureEqualTerm :: Type -> Term -> Term -> TCM Bool #-}
pureEqualTerm
  :: (PureTCM m, MonadBlock m)
  => Type -> Term -> Term -> m Bool
pureEqualTerm a u v =
  isJust <$> runPureConversion (equalTerm a u v)

{-# SPECIALIZE pureEqualTermB :: Type -> Term -> Term -> TCM (Either Blocker Bool) #-}
-- | Return the blocker instead of throwing a `patternViolation`.
pureEqualTermB :: PureTCM m => Type -> Term -> Term -> m (Either Blocker Bool)
pureEqualTermB a u v =
  fmap isJust <$> runPureConversionB (equalTerm a u v)

{-# SPECIALIZE pureEqualType :: Type -> Type -> TCM Bool #-}
pureEqualType
  :: (PureTCM m, MonadBlock m)
  => Type -> Type -> m Bool
pureEqualType a b =
  isJust <$> runPureConversion (equalType a b)

{-# SPECIALIZE pureEqualType :: Type -> Type -> TCM Bool #-}
-- | Return the blocker instead of throwing a `patternViolation`.
pureEqualTypeB :: PureTCM m => Type -> Type -> m (Either Blocker Bool)
pureEqualTypeB a b =
  fmap isJust <$> runPureConversionB (equalType a b)

{-# SPECIALIZE pureCompareAs :: Comparison -> CompareAs -> Term -> Term -> TCM Bool #-}
pureCompareAs
  :: (PureTCM m, MonadBlock m)
  => Comparison -> CompareAs -> Term -> Term -> m Bool
pureCompareAs cmp a u v =
  isJust <$> runPureConversion (compareAs cmp a u v)

{-# SPECIALIZE runPureConversion :: PureConversionT TCM a -> TCM (Maybe a) #-}
runPureConversion
  :: (MonadBlock m, PureTCM m)
  => PureConversionT m a -> m (Maybe a)
runPureConversion m = either patternViolation pure =<< runPureConversionB m

{-# SPECIALIZE runPureConversionB :: PureConversionT TCM a -> TCM (Either Blocker (Maybe a)) #-}
runPureConversionB :: PureTCM m => PureConversionT m a -> m (Either Blocker (Maybe a))
runPureConversionB (PureConversionT m) = locallyTC eCompareBlocked (const True) $
  verboseBracket "tc.conv.pure" 40 "runPureConversion" $ do
  i <- useR stFreshInt
  pid <- useR stFreshProblemId
  nid <- useR stFreshNameId
  let frsh = FreshThings i pid nid
  result <- fst <$> runStateT (runExceptT m) frsh
  case result of
    Left (PatternErr block)
     | block == neverUnblock -> do
         debugResult "stuck"
         return $ Right Nothing
     | otherwise             -> do
         debugResult $ "blocked on" <+> prettyTCM block
         return $ Left block
    Left TypeError{}         -> do
      debugResult "type error"
      return $ Right Nothing
    Left GenericException{}  -> __IMPOSSIBLE__
    Left IOException{}       -> __IMPOSSIBLE__
    Left ParserError{}       -> __IMPOSSIBLE__
    Right x                  -> do
      debugResult "success"
      return $ Right $ Just x
  where
    debugResult msg = reportSDoc "tc.conv.pure" 40 $ "runPureConversion result: " <+> msg

instance MonadTrans PureConversionT where
  lift = PureConversionT . lift . lift

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

instance Monad m => MonadBlock (PureConversionT m) where
  patternViolation = throwError . PatternErr
  catchPatternErr handle m = m `catchError` \case
    PatternErr b -> handle b
    err          -> throwError err


instance PureTCM m => MonadConstraint (PureConversionT m) where
  addConstraint u _ = patternViolation u
  addAwakeConstraint u _ = patternViolation u
  solveConstraint c = patternViolation alwaysUnblock  -- TODO: does this happen?
  solveSomeAwakeConstraints _ _ = return ()
  wakeConstraints _ = return ()
  stealConstraints _ = return ()
  modifyAwakeConstraints _ = patternViolation alwaysUnblock  -- TODO: does this happen?
  modifySleepingConstraints _ = patternViolation alwaysUnblock  -- TODO: does this happen?

instance PureTCM m => MonadMetaSolver (PureConversionT m) where
  newMeta' _ _ _ _ _ _ = patternViolation alwaysUnblock  -- TODO: does this happen?
  assignV _ m _ v _ = do
    bv <- isBlocked v
    let blocker = caseMaybe bv id unblockOnEither $ unblockOnMeta m
    patternViolation blocker
  assignTerm' m _ v = do
    bv <- isBlocked v
    let blocker = caseMaybe bv id unblockOnEither $ unblockOnMeta m
    patternViolation blocker
  etaExpandMeta _ _ = return ()
  updateMetaVar _ _ = patternViolation alwaysUnblock  -- TODO: does this happen?
  speculateMetas fallback m = m >>= \case
    KeepMetas     -> return ()
    RollBackMetas -> fallback

instance PureTCM m => MonadInteractionPoints (PureConversionT m) where
  freshInteractionId = patternViolation alwaysUnblock  -- TODO: does this happen?
  modifyInteractionPoints _ = patternViolation alwaysUnblock  -- TODO: does this happen?

-- This is a bogus instance that promptly forgets all concrete names,
-- but we don't really care
instance ReadTCState m => MonadStConcreteNames (PureConversionT m) where
  runStConcreteNames m = do
    concNames <- useR stConcreteNames
    fst <$> runStateT m concNames

instance PureTCM m => MonadWarning (PureConversionT m) where
  addWarning w = case classifyWarning (tcWarning w) of
    ErrorWarnings -> patternViolation neverUnblock
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

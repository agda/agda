
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Reduce.Monad
  ( constructorForm
  , enterClosure
  , getConstInfo
  , askR, applyWhenVerboseS
  ) where

import Prelude hiding (null)

import Control.Monad         ( liftM2 )

import qualified Data.Map as Map
import Data.Maybe

import System.IO.Unsafe

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad hiding (enterClosure, constructorForm)
import Agda.TypeChecking.Substitute

import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.Pretty () --instance only


instance HasBuiltins ReduceM where
  getBuiltinThing b = liftM2 mplus (Map.lookup b <$> useR stLocalBuiltins)
                                   (Map.lookup b <$> useR stImportedBuiltins)

constructorForm :: HasBuiltins m => Term -> m Term
constructorForm v = do
  mz <- getBuiltin' builtinZero
  ms <- getBuiltin' builtinSuc
  return $ fromMaybe v $ constructorForm' mz ms v

enterClosure :: LensClosure a c => c -> (a -> ReduceM b) -> ReduceM b
enterClosure c | Closure _sig env scope cps x <- c ^. lensClosure = \case
  -- The \case is a hack to correctly associate the where block to the rhs
  -- rather than to the expression in the pattern guard.
  f -> localR (mapRedEnvSt inEnv inState) (f x)
    where
    inEnv   e = env
    inState s =
      -- TODO: use the signature here? would that fix parts of issue 118?
      set stScope scope $ set stModuleCheckpoints cps s

withFreshR :: (ReadTCState m, HasFresh i) => (i -> m a) -> m a
withFreshR f = do
  s <- getTCState
  let (i, s') = nextFresh s
  withTCState (const s') (f i)

instance MonadAddContext ReduceM where
  withFreshName r s k = withFreshR $ \i -> k (mkName r i s)

  addCtx = defaultAddCtx

  addLetBinding' = defaultAddLetBinding'

  updateContext rho f ret = withFreshR $ \ chkpt ->
    localTC (\e -> e { envContext = f $ envContext e
                     , envCurrentCheckpoint = chkpt
                     , envCheckpoints = Map.insert chkpt IdS $
                                          fmap (applySubst rho) (envCheckpoints e)
                     }) ret
        -- let-bindings keep track of own their context

instance MonadDebug ReduceM where

  traceDebugMessage k n s cont = do
    ReduceEnv env st _ <- askR
    unsafePerformIO $ do
      _ <- runTCM env st $ displayDebugMessage k n s
      return $ cont

  formatDebugMessage k n d = do
    ReduceEnv env st _ <- askR
    unsafePerformIO $ do
      (s , _) <- runTCM env st $ formatDebugMessage k n d
      return $ return s

  verboseBracket k n s = applyWhenVerboseS k n $
    bracket_ (openVerboseBracket k n s) (const $ closeVerboseBracket k n)

  getVerbosity      = defaultGetVerbosity
  getProfileOptions = defaultGetProfileOptions
  isDebugPrinting   = defaultIsDebugPrinting
  nowDebugPrinting  = defaultNowDebugPrinting

instance HasConstInfo ReduceM where
  getRewriteRulesFor = defaultGetRewriteRulesFor
  getConstInfo' q = do
    ReduceEnv env st _ <- askR
    defaultGetConstInfo st env q

instance PureTCM ReduceM where

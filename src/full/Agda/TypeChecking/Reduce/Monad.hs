{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Reduce.Monad
  ( enterClosure
  , getConstInfo
  , askR, applyWhenVerboseS
  ) where

import Prelude hiding (null)

import qualified Data.Map as Map

import System.IO.Unsafe

import Agda.Syntax.Common.Pretty () --instance only
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute

import Agda.Utils.Maybe
import Agda.Utils.Monad

instance HasBuiltins ReduceM where
  getBuiltinThing b =
    liftM2 (unionMaybeWith unionBuiltin)
      (Map.lookup b <$> useR stLocalBuiltins)
      (Map.lookup b <$> useR stImportedBuiltins)

withFreshR :: (ReadTCState m, HasFresh i) => (i -> m a) -> m a
withFreshR f = do
  s <- getTCState
  let (i, s') = nextFresh s
  withTCState (const s') (f i)

instance MonadAddContext ReduceM where
  withFreshName r s k = withFreshR $ \i -> k (mkName r i s)

  addCtx = defaultAddCtx

  addLetBinding' = defaultAddLetBinding'

  addLocalRewrite = defaultAddLocalRewrite

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

#ifdef DEBUG
  verboseBracket k n s = applyWhenVerboseS k n $
    bracket_ (openVerboseBracket k n s) (const $ closeVerboseBracket k n)
#else
  verboseBracket k n s ma = ma
  {-# INLINE verboseBracket #-}
#endif

  getVerbosity      = defaultGetVerbosity
  getProfileOptions = defaultGetProfileOptions
  isDebugPrinting   = defaultIsDebugPrinting
  nowDebugPrinting  = defaultNowDebugPrinting

instance HasConstInfo ReduceM where
  getRewriteRulesFor      = defaultGetRewriteRulesFor
  getLocalRewriteRulesFor = defaultGetLocalRewriteRulesFor
  getConstInfo' q = do
    ReduceEnv env st _ <- askR
    defaultGetConstInfo st env q

instance PureTCM ReduceM where

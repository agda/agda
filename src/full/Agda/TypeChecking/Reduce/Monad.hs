
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Reduce.Monad
  ( constructorForm
  , enterClosure
  , getConstInfo
  , isInstantiatedMeta
  , lookupMeta
  , askR, applyWhenVerboseS
  ) where

import Prelude hiding (null)

import Control.Arrow ((***), first, second)
import Control.Applicative hiding (empty)
import Control.Monad.Reader

import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid

import Debug.Trace
import System.IO.Unsafe

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad hiding
  ( enterClosure, isInstantiatedMeta, verboseS, typeOfConst, lookupMeta, lookupMeta' )
import Agda.TypeChecking.Monad.Builtin hiding ( constructorForm )
import Agda.TypeChecking.Substitute
import Agda.Interaction.Options

import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty

import Agda.Utils.Impossible

instance HasBuiltins ReduceM where
  getBuiltinThing b = liftM2 mplus (Map.lookup b <$> useR stLocalBuiltins)
                                   (Map.lookup b <$> useR stImportedBuiltins)

constructorForm :: HasBuiltins m => Term -> m Term
constructorForm v = do
  mz <- getBuiltin' builtinZero
  ms <- getBuiltin' builtinSuc
  return $ fromMaybe v $ constructorForm' mz ms v

enterClosure :: Closure a -> (a -> ReduceM b) -> ReduceM b
enterClosure (Closure sig env scope cps x) f = localR (mapRedEnvSt inEnv inState) (f x)
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

  updateContext rho f ret = withFreshR $ \ chkpt ->
    localTC (\e -> e { envContext = f $ envContext e
                     , envCurrentCheckpoint = chkpt
                     , envCheckpoints = Map.insert chkpt IdS $
                                          fmap (applySubst rho) (envCheckpoints e)
                     }) ret
        -- let-bindings keep track of own their context

lookupMeta' :: MetaId -> ReduceM (Maybe MetaVariable)
lookupMeta' (MetaId i) = IntMap.lookup i <$> useR stMetaStore

lookupMeta :: MetaId -> ReduceM MetaVariable
lookupMeta = fromMaybe __IMPOSSIBLE__ <.> lookupMeta'

isInstantiatedMeta :: MetaId -> ReduceM Bool
isInstantiatedMeta i = do
  mv <- lookupMeta i
  return $ case mvInstantiation mv of
    InstV{} -> True
    _       -> False

instance MonadDebug ReduceM where

  traceDebugMessage n s cont = do
    ReduceEnv env st <- askR
    unsafePerformIO $ do
      _ <- runTCM env st $ displayDebugMessage n s
      return $ cont

  formatDebugMessage k n d = do
    ReduceEnv env st <- askR
    unsafePerformIO $ do
      (s , _) <- runTCM env st $ formatDebugMessage k n d
      return $ return s

  verboseBracket k n s = applyWhenVerboseS k n $
    bracket_ (openVerboseBracket n s) (const $ closeVerboseBracket n)

instance HasConstInfo ReduceM where
  getRewriteRulesFor = defaultGetRewriteRulesFor getTCState
  getConstInfo' q = do
    ReduceEnv env st <- askR
    defaultGetConstInfo st env q

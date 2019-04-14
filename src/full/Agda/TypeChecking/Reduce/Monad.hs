{-# LANGUAGE CPP              #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Reduce.Monad
  ( constructorForm
  , enterClosure
  , underAbstraction , underAbstraction_
  , addCtxTel
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
  ( enterClosure, underAbstraction_, underAbstraction, addCtx,
    isInstantiatedMeta, verboseS, typeOfConst, lookupMeta, lookupMeta' )
import Agda.TypeChecking.Monad.Builtin hiding ( constructorForm )
import Agda.TypeChecking.Substitute
import Agda.Interaction.Options

import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty

#include "undefined.h"
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

withFreshName :: (MonadReduce m) => Range -> ArgName -> (Name -> m a) -> m a
withFreshName r s k = withFreshR $ \i -> k (mkName r i s)

withFreshName_ :: (MonadReduce m) => ArgName -> (Name -> m a) -> m a
withFreshName_ = withFreshName noRange

addCtx :: (MonadReduce m) => Name -> Dom Type -> m a -> m a
addCtx x a ret = do
  ctx <- asksTC $ map (fst . unDom) . envContext
  let ce = (x,) <$> a
  oldChkpt <- viewTC eCurrentCheckpoint
  withFreshR $ \ chkpt ->
    localTC (\e -> e { envContext = ce : envContext e
                   , envCurrentCheckpoint = chkpt
                   , envCheckpoints = Map.insert chkpt IdS $
                                        fmap (raise 1) (envCheckpoints e)
                   }) ret
      -- let-bindings keep track of own their context

addCtxTel :: (MonadReduce m) => Telescope -> m a -> m a
addCtxTel EmptyTel          ret = ret
addCtxTel (ExtendTel t tel) ret = underAbstraction t tel $ \tel -> addCtxTel tel ret

underAbstraction :: (MonadReduce m, Subst t a) => Dom Type -> Abs a -> (a -> m b) -> m b
underAbstraction _ (NoAbs _ v) f = f v
underAbstraction t a f =
  withFreshName_ (realName $ absName a) $ \x -> addCtx x t $ f (absBody a)
  where
    realName s = if isNoName s then "x" else s

underAbstraction_ :: (MonadReduce m, Subst t a) => Abs a -> (a -> m b) -> m b
underAbstraction_ = underAbstraction __DUMMY_DOM__

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

-- | Apply a function if a certain verbosity level is activated.
--
--   Precondition: The level must be non-negative.
{-# SPECIALIZE applyWhenVerboseS :: VerboseKey -> Int -> (ReduceM a -> ReduceM a) -> ReduceM a-> ReduceM a #-}
applyWhenVerboseS :: HasOptions m => VerboseKey -> Int -> (m a -> m a) -> m a -> m a
applyWhenVerboseS k n f a = ifM (hasVerbosity k n) (f a) a

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

instance HasConstInfo ReduceM where
  getRewriteRulesFor = defaultGetRewriteRulesFor getTCState
  getConstInfo' q = do
    ReduceEnv env st <- askR
    defaultGetConstInfo st env q

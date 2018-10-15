{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Signature where

#if __GLASGOW_HASKELL__ >= 800
import qualified Control.Monad.Fail as Fail
#endif

import Control.Monad.Reader

import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Internal (ModuleName, Telescope)

import Agda.TypeChecking.Monad.Base
  ( TCM, ReadTCState, HasOptions, TCEnv, MonadTCEnv
  , Definition, RewriteRules
  )
import Agda.TypeChecking.Monad.Debug (MonadDebug)

import Agda.Utils.Pretty (prettyShow)

data SigError = SigUnknown String | SigAbstract

class ( Functor m
      , Applicative m
#if __GLASGOW_HASKELL__ == 710
      , Monad m
#else
      , Fail.MonadFail m
#endif
      , HasOptions m
      , MonadDebug m
      , MonadTCEnv m
      ) => HasConstInfo m where
  getConstInfo :: QName -> m Definition
  getConstInfo q = getConstInfo' q >>= \case
      Right d -> return d
      Left (SigUnknown err) -> __IMPOSSIBLE_VERBOSE__ err
      Left SigAbstract      -> __IMPOSSIBLE_VERBOSE__ $
        "Abstract, thus, not in scope: " ++ prettyShow q
  getConstInfo' :: QName -> m (Either SigError Definition)
  getConstInfo' q = Right <$> getConstInfo q
  getRewriteRulesFor :: QName -> m RewriteRules

inFreshModuleIfFreeParams :: TCM a -> TCM a
lookupSection :: (Functor m, ReadTCState m) => ModuleName -> m Telescope


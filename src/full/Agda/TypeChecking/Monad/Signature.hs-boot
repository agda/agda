{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Monad.Signature where

import Control.Monad.Reader
import Control.Monad.State

import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal (ModuleName, Telescope, RewriteHead)

import Agda.TypeChecking.Monad.Base
  ( TCM, ReadTCState, HasOptions, MonadTCEnv
  , Definition, GlobalRewriteRules, RewriteRules
  )
import {-# SOURCE #-} Agda.TypeChecking.Monad.Debug (MonadDebug)

import Agda.Utils.CallStack (HasCallStack)

data SigError = SigUnknown String | SigAbstract | SigCubicalNotErasure

notSoPrettySigCubicalNotErasure :: QName -> String

class ( Functor m
      , Applicative m
      , HasOptions m
      , MonadDebug m
      , MonadTCEnv m
      ) => HasConstInfo m where
  getConstInfo :: HasCallStack => QName -> m Definition
  getConstInfo q = getConstInfo' q >>= \case
      Right d -> return d
      Left (SigUnknown err) -> __IMPOSSIBLE_VERBOSE__ err
      Left SigAbstract      -> __IMPOSSIBLE_VERBOSE__ $
        "Abstract, thus, not in scope: " ++ prettyShow q
      Left SigCubicalNotErasure -> __IMPOSSIBLE_VERBOSE__ $
        notSoPrettySigCubicalNotErasure q

  getConstInfo' :: HasCallStack => QName -> m (Either SigError Definition)
  -- getConstInfo' q = Right <$> getConstInfo q
  getGlobalRewriteRulesFor :: QName -> m GlobalRewriteRules
  getLocalRewriteRulesFor :: RewriteHead -> m RewriteRules

  default getConstInfo' :: (HasCallStack, HasConstInfo n, MonadTrans t, m ~ t n) => QName -> m (Either SigError Definition)
  getConstInfo' = lift . getConstInfo'

  default getGlobalRewriteRulesFor :: (HasConstInfo n, MonadTrans t, m ~ t n) => QName -> m GlobalRewriteRules
  getGlobalRewriteRulesFor = lift . getGlobalRewriteRulesFor

  default getLocalRewriteRulesFor :: (HasConstInfo n, MonadTrans t, m ~ t n) => RewriteHead -> m RewriteRules
  getLocalRewriteRulesFor = lift . getLocalRewriteRulesFor

instance HasConstInfo m => HasConstInfo (ReaderT r m)
instance HasConstInfo m => HasConstInfo (StateT s m)

instance HasConstInfo TCM where

inFreshModuleIfFreeParams :: TCM a -> TCM a
lookupSection :: (ReadTCState m) => ModuleName -> m Telescope

-- | General functions for stateful manipulation of the scope.

-- This module has been originally created to avoid import cycles between
-- Agda.Syntax.Scope.Monad and Agda.Syntax.Scope.UnusedImports.

module Agda.Syntax.Scope.State where

import Agda.Syntax.Abstract.Name as A ( ModuleName )
import Agda.Syntax.Position ( SetRange(setRange), noRange )
import Agda.Syntax.Scope.Base (scopeCurrent)

import Agda.TypeChecking.Monad.Base ( TCM, MonadTCState, ReadTCState )
import Agda.TypeChecking.Monad.State (useScope, modifyScope, recomputeInverseScope)

import Agda.Utils.Lens (set)
import Agda.Utils.Monad (MonadTrans (lift))

---------------------------------------------------------------------------
-- * The scope checking monad
---------------------------------------------------------------------------

-- | To simplify interaction between scope checking and type checking (in
--   particular when chasing imports), we use the same monad.
type ScopeM = TCM

---------------------------------------------------------------------------
-- * Current module
---------------------------------------------------------------------------

getCurrentModule :: ReadTCState m => m A.ModuleName
getCurrentModule = setRange noRange <$> useScope scopeCurrent

setCurrentModule :: MonadTCState m => A.ModuleName -> m ()
setCurrentModule m = do
  modifyScope $ set scopeCurrent m
  recomputeInverseScope

withCurrentModule :: (ReadTCState m, MonadTCState m) => A.ModuleName -> m a -> m a
withCurrentModule new action = do
  old <- getCurrentModule
  setCurrentModule new
  x   <- action
  setCurrentModule old
  return x

withCurrentModule' :: (MonadTrans t, Monad (t ScopeM)) => A.ModuleName -> t ScopeM a -> t ScopeM a
withCurrentModule' new action = do
  old <- lift getCurrentModule
  lift $ setCurrentModule new
  x   <- action
  lift $ setCurrentModule old
  return x

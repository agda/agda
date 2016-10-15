{-# LANGUAGE CPP #-}

#if !(MIN_VERSION_mtl(2,2,1))
{-# OPTIONS_GHC -fno-warn-orphans #-}
#endif

------------------------------------------------------------------------------
-- | Wrapper for Control.Monad.Except from the mtl package
------------------------------------------------------------------------------

module Agda.Utils.Except
  ( Error(noMsg, strMsg)
  , ExceptT
  , mkExceptT
  , MonadError(catchError, throwError)
  , runExceptT
  , mapExceptT
  ) where

#include "undefined.h"
import Agda.Utils.Impossible

------------------------------------------------------------------------
#if MIN_VERSION_mtl(2,2,1)
-- New mtl, reexport ExceptT, define class Error for backward compat.
------------------------------------------------------------------------

import Control.Monad.Except

-- | We cannot define data constructors synonymous, so we define the
-- @mkExceptT@ function to be used instead of the data constructor
-- @ExceptT@.
mkExceptT :: m (Either e a) -> ExceptT e m a
mkExceptT = ExceptT

-- From Control.Monad.Trans.Error of transformers 0.3.0.0.

class Error a where
  noMsg  :: a
  strMsg :: String -> a

  noMsg    = strMsg ""
  strMsg _ = noMsg

-- | A string can be thrown as an error.
instance Error String where
  strMsg = id

------------------------------------------------------------------------
#else
-- Old mtl, need to define ExceptT from ErrorT
------------------------------------------------------------------------

import Control.Monad.Error
import Text.PrettyPrint

type ExceptT = ErrorT

-- | We cannot define data constructors synonymous, so we define the
-- @mkExceptT@ function to be used instead of the data constructor
-- @ErrorT@.
mkExceptT :: m (Either e a) -> ExceptT e m a
mkExceptT = ErrorT

-- | 'runExcept' function using mtl 2.1.*.
runExceptT ::  ExceptT e m a -> m (Either e a)
runExceptT = runErrorT

mapExceptT :: (m (Either e a) -> m' (Either e' a')) -> ExceptT e m a -> ExceptT e' m' a'
mapExceptT = mapErrorT

instance Error Doc where
  noMsg  = empty
  strMsg = text

-- | To simulate @MaybeT@ by @ExceptT@.
instance Error () where
  noMsg = ()

-- Stupid ErrorT!
instance Error (a, b, c) where
  noMsg = __IMPOSSIBLE__

#endif

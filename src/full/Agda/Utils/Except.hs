
------------------------------------------------------------------------------
-- | Wrapper for Control.Monad.Except from the mtl library (>= 2.2.1)
------------------------------------------------------------------------------

module Agda.Utils.Except
  ( ExceptT
  , mapExceptT
  , mkExceptT
  , MonadError(catchError, throwError)
  , runExceptT
  ) where

import Control.Monad.Except

------------------------------------------------------------------------

-- | We cannot define data constructors synonymous, so we define the
-- @mkExceptT@ function to be used instead of the data constructor
-- @ExceptT@.
mkExceptT :: m (Either e a) -> ExceptT e m a
mkExceptT = ExceptT

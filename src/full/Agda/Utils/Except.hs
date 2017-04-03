
------------------------------------------------------------------------------
-- | Wrapper for Control.Monad.Except from the mtl library (>= 2.2.1)
------------------------------------------------------------------------------

module Agda.Utils.Except
  ( Error(noMsg, strMsg)
  , ExceptT
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

-- | Error class for backward compatibility (from
-- Control.Monad.Trans.Error in transformers 0.3.0.0).

class Error a where
  noMsg  :: a
  strMsg :: String -> a

  noMsg    = strMsg ""
  strMsg _ = noMsg

-- | A string can be thrown as an error.
instance Error String where
  strMsg = id

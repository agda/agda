------------------------------------------------------------------------------
-- | Wrapper for Control.Monad.Except from mtl >= 2.2.1
------------------------------------------------------------------------------

module Agda.Utils.Except
  ( Error(noMsg, strMsg)
  , ExceptT(ExceptT)
  , MonadError(catchError, throwError)
  , runExceptT
  ) where

import Control.Monad.Except

-- From Control.Monad.Trans.Error of transformers 0.3.0.0.

class Error a where
  noMsg  :: a
  strMsg :: String -> a

  noMsg    = strMsg ""
  strMsg _ = noMsg

-- | A string can be thrown as an error.
instance ErrorList a => Error [a] where
    strMsg = listMsg

-- | Workaround so that we can have a Haskell 98 instance @'Error' 'String'@.
class ErrorList a where
    listMsg :: String -> [a]

instance ErrorList Char where
    listMsg = id

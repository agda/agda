{-# LANGUAGE CPP #-}

------------------------------------------------------------------------------
-- | Wrapper for Control.Monad.Except from the mtl package
------------------------------------------------------------------------------

module Agda.Utils.Except
  ( Error(noMsg, strMsg)
  , ExceptT
  , MonadError(catchError, throwError)
  , runExceptT
  ) where

#if MIN_VERSION_mtl(2,2,1)
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

#else
import Control.Monad.Error

type ExceptT = ErrorT

-- | 'runExcept' function using mtl 2.1.*.
runExceptT ::  ExceptT e m a -> m (Either e a)
runExceptT = runErrorT
#endif

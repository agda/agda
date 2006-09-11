
module TypeChecking.Monad.Builtin where

import Control.Monad.State
import qualified Data.Map as Map

import Syntax.Internal
import TypeChecking.Monad.Base

getBuiltinThings :: TCM BuiltinThings
getBuiltinThings = gets stBuiltinThings

setBuiltinThings :: BuiltinThings -> TCM ()
setBuiltinThings b = modify $ \s -> s { stBuiltinThings = b }

bindBuiltinName :: String -> Term -> TCM ()
bindBuiltinName b x = do
	builtin <- getBuiltinThings
	case Map.lookup b builtin of
	    Just y  -> typeError $ DuplicateBuiltinBinding b y x
	    Nothing -> setBuiltinThings $ Map.insert b x builtin

getBuiltin :: String -> TCM Term
getBuiltin x = do
    builtin <- getBuiltinThings
    case Map.lookup x builtin of
	Nothing	-> typeError $ NoBindingForBuiltin x
	Just t	-> return t


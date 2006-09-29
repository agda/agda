
module TypeChecking.Monad.Builtin where

import Control.Monad.State
import qualified Data.Map as Map

import Syntax.Internal
import TypeChecking.Monad.Base

getBuiltinThings :: TCM (BuiltinThings PrimFun)
getBuiltinThings = gets stBuiltinThings

setBuiltinThings :: BuiltinThings PrimFun -> TCM ()
setBuiltinThings b = modify $ \s -> s { stBuiltinThings = b }

bindBuiltinName :: String -> Term -> TCM ()
bindBuiltinName b x = do
	builtin <- getBuiltinThings
	case Map.lookup b builtin of
	    Just (Builtin y) -> typeError $ DuplicateBuiltinBinding b y x
	    Just (Prim _)    -> typeError $ NoSuchBuiltinName b
	    Nothing	     -> setBuiltinThings $ Map.insert b (Builtin x) builtin

bindPrimitive :: String -> PrimFun -> TCM ()
bindPrimitive b pf = do
	builtin <- getBuiltinThings
	case Map.lookup b builtin :: Maybe (Builtin PrimFun) of
	    _ -> setBuiltinThings $ Map.insert b (Prim pf) builtin


getBuiltin :: String -> TCM Term
getBuiltin x = do
    builtin <- getBuiltinThings
    case Map.lookup x builtin of
	Just (Builtin t) -> return t
	_		 -> typeError $ NoBindingForBuiltin x

getPrimitive :: String -> TCM PrimFun
getPrimitive x = do
    builtin <- getBuiltinThings
    case Map.lookup x builtin of
	Just (Prim pf) -> return pf
	_	       -> typeError $ NoSuchPrimitiveFunction x


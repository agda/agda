
module TypeChecking.Monad.Builtin where

import Control.Monad.State
import qualified Data.Map as Map

import Syntax.Internal
import TypeChecking.Monad.Base

getBuiltinThings :: MonadTCM tcm => tcm (BuiltinThings PrimFun)
getBuiltinThings = gets stBuiltinThings

setBuiltinThings :: MonadTCM tcm => BuiltinThings PrimFun -> tcm ()
setBuiltinThings b = modify $ \s -> s { stBuiltinThings = b }

bindBuiltinName :: MonadTCM tcm => String -> Term -> tcm ()
bindBuiltinName b x = do
	builtin <- getBuiltinThings
	case Map.lookup b builtin of
	    Just (Builtin y) -> typeError $ DuplicateBuiltinBinding b y x
	    Just (Prim _)    -> typeError $ NoSuchBuiltinName b
	    Nothing	     -> setBuiltinThings $ Map.insert b (Builtin x) builtin

bindPrimitive :: MonadTCM tcm => String -> PrimFun -> tcm ()
bindPrimitive b pf = do
	builtin <- getBuiltinThings
	case Map.lookup b builtin :: Maybe (Builtin PrimFun) of
	    _ -> setBuiltinThings $ Map.insert b (Prim pf) builtin


getBuiltin :: MonadTCM tcm => String -> tcm Term
getBuiltin x = do
    mt <- getBuiltin' x
    case mt of
        Nothing -> typeError $ NoBindingForBuiltin x
        Just t  -> return t

getBuiltin' :: MonadTCM tcm => String -> tcm (Maybe Term)
getBuiltin' x = do
    builtin <- getBuiltinThings
    case Map.lookup x builtin of
	Just (Builtin t) -> return $ Just t
	_		 -> return Nothing

getPrimitive :: MonadTCM tcm => String -> tcm PrimFun
getPrimitive x = do
    builtin <- getBuiltinThings
    case Map.lookup x builtin of
	Just (Prim pf) -> return pf
	_	       -> typeError $ NoSuchPrimitiveFunction x

---------------------------------------------------------------------------
-- * The names of built-in things
---------------------------------------------------------------------------

primInteger, primFloat, primChar, primString, primBool, primTrue, primFalse,
    primList, primNil, primCons, primIO, primUnit, primNat, primSuc, primZero,
    primNatPlus, primNatMinus, primNatTimes, primNatDivSuc, primNatModSuc,
    primNatEquality, primNatLess, primEqual, primRefl
    :: MonadTCM tcm => tcm Term
primInteger     = getBuiltin builtinInteger
primFloat       = getBuiltin builtinFloat
primChar        = getBuiltin builtinChar
primString      = getBuiltin builtinString
primBool        = getBuiltin builtinBool
primTrue        = getBuiltin builtinTrue
primFalse       = getBuiltin builtinFalse
primList        = getBuiltin builtinList
primNil         = getBuiltin builtinNil
primCons        = getBuiltin builtinCons
primIO          = getBuiltin builtinIO
primUnit        = getBuiltin builtinUnit
primNat         = getBuiltin builtinNat
primSuc         = getBuiltin builtinSuc
primZero        = getBuiltin builtinZero
primNatPlus     = getBuiltin builtinNatPlus
primNatMinus    = getBuiltin builtinNatMinus
primNatTimes    = getBuiltin builtinNatTimes
primNatDivSuc   = getBuiltin builtinNatDivSuc
primNatModSuc   = getBuiltin builtinNatModSuc
primNatEquality = getBuiltin builtinNatEquals
primNatLess     = getBuiltin builtinNatLess
primEqual       = getBuiltin builtinEquality
primRefl        = getBuiltin builtinRefl

builtinNat       = "NATURAL"
builtinSuc       = "SUC"
builtinZero      = "ZERO"
builtinNatPlus   = "NATPLUS"
builtinNatMinus  = "NATMINUS"
builtinNatTimes  = "NATTIMES"
builtinNatDivSuc = "NATDIVSUC"
builtinNatModSuc = "NATMODSUC"
builtinNatEquals = "NATEQUALS"
builtinNatLess   = "NATLESS"
builtinInteger   = "INTEGER"
builtinFloat     = "FLOAT"
builtinChar      = "CHAR"
builtinString    = "STRING"
builtinBool      = "BOOL"
builtinTrue      = "TRUE"
builtinFalse     = "FALSE"
builtinList      = "LIST"
builtinNil       = "NIL"
builtinCons      = "CONS"
builtinIO        = "IO"
builtinUnit      = "UNIT"
builtinEquality	 = "EQUAL"
builtinRefl	 = "REFL"

builtinTypes :: [String]
builtinTypes =
    [ builtinInteger
    , builtinFloat
    , builtinChar
    , builtinString
    , builtinBool
    , builtinUnit
    , builtinNat
    ]


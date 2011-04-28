
module Agda.TypeChecking.Monad.Builtin where

import Data.Functor
import Control.Monad.State
import qualified Data.Map as Map

import Agda.Syntax.Position
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base

getBuiltinThing :: MonadTCM tcm => String -> tcm (Maybe (Builtin PrimFun))
getBuiltinThing b = liftM2 mplus (Map.lookup b <$> gets stLocalBuiltins)
                    (Map.lookup b <$> gets stImportedBuiltins)

setBuiltinThings :: MonadTCM tcm => BuiltinThings PrimFun -> tcm ()
setBuiltinThings b = modify $ \s -> s { stLocalBuiltins = b }

bindBuiltinName :: MonadTCM tcm => String -> Term -> tcm ()
bindBuiltinName b x = do
	builtin <- getBuiltinThing b
	case builtin of
	    Just (Builtin y) -> typeError $ DuplicateBuiltinBinding b y x
	    Just (Prim _)    -> typeError $ NoSuchBuiltinName b
	    Nothing	     -> modify $ \st ->
              st { stLocalBuiltins =
                    Map.insert b (Builtin x) $ stLocalBuiltins st
                 }

bindPrimitive :: MonadTCM tcm => String -> PrimFun -> tcm ()
bindPrimitive b pf = do
  builtin <- gets stLocalBuiltins
  setBuiltinThings $ Map.insert b (Prim pf) builtin


getBuiltin :: MonadTCM tcm => String -> tcm Term
getBuiltin x = do
    mt <- getBuiltin' x
    case mt of
        Nothing -> typeError $ NoBindingForBuiltin x
        Just t  -> return t

getBuiltin' :: MonadTCM tcm => String -> tcm (Maybe Term)
getBuiltin' x = do
    builtin <- getBuiltinThing x
    case builtin of
	Just (Builtin t) -> return $ Just (killRange t)
	_		 -> return Nothing

getPrimitive :: MonadTCM tcm => String -> tcm PrimFun
getPrimitive x = do
    builtin <- getBuiltinThing x
    case builtin of
	Just (Prim pf) -> return pf
	_	       -> typeError $ NoSuchPrimitiveFunction x

---------------------------------------------------------------------------
-- * The names of built-in things
---------------------------------------------------------------------------

primInteger, primFloat, primChar, primString, primBool, primTrue, primFalse,
    primList, primNil, primCons, primIO, primNat, primSuc, primZero,
    primNatPlus, primNatMinus, primNatTimes, primNatDivSucAux, primNatModSucAux,
    primNatEquality, primNatLess, primSize, primSizeSuc, primSizeInf,
    primInf, primSharp, primFlat,
    primEquality, primRefl,
    primLevel, primLevelZero, primLevelSuc, primLevelMax,
    -- builtins for reflection:
    primQName, primArg, primArgArg, primAgdaTerm, primAgdaTermVar,
    primAgdaTermLam, primAgdaTermDef, primAgdaTermCon, primAgdaTermPi,
    primAgdaTermSort, primAgdaTermUnsupported,
    primAgdaType, primAgdaTypeEl,
    primHiding, primHidden, primVisible,
    primRelvance, primRelevant, primIrrelevant, primForced,
    primAgdaSort, primAgdaSortSet, primAgdaSortLit, primAgdaSortUnsupported
    :: MonadTCM tcm => tcm Term
primInteger      = getBuiltin builtinInteger
primFloat        = getBuiltin builtinFloat
primChar         = getBuiltin builtinChar
primString       = getBuiltin builtinString
primBool         = getBuiltin builtinBool
primTrue         = getBuiltin builtinTrue
primFalse        = getBuiltin builtinFalse
primList         = getBuiltin builtinList
primNil          = getBuiltin builtinNil
primCons         = getBuiltin builtinCons
primIO           = getBuiltin builtinIO
primNat          = getBuiltin builtinNat
primSuc          = getBuiltin builtinSuc
primZero         = getBuiltin builtinZero
primNatPlus      = getBuiltin builtinNatPlus
primNatMinus     = getBuiltin builtinNatMinus
primNatTimes     = getBuiltin builtinNatTimes
primNatDivSucAux = getBuiltin builtinNatDivSucAux
primNatModSucAux = getBuiltin builtinNatModSucAux
primNatEquality  = getBuiltin builtinNatEquals
primNatLess      = getBuiltin builtinNatLess
primSize         = getBuiltin builtinSize
primSizeSuc      = getBuiltin builtinSizeSuc
primSizeInf      = getBuiltin builtinSizeInf
primInf          = getBuiltin builtinInf
primSharp        = getBuiltin builtinSharp
primFlat         = getBuiltin builtinFlat
primEquality     = getBuiltin builtinEquality
primRefl         = getBuiltin builtinRefl
primLevel        = getBuiltin builtinLevel
primLevelZero    = getBuiltin builtinLevelZero
primLevelSuc     = getBuiltin builtinLevelSuc
primLevelMax     = getBuiltin builtinLevelMax
primQName        = getBuiltin builtinQName
primArg          = getBuiltin builtinArg
primArgArg       = getBuiltin builtinArgArg
primAgdaSort     = getBuiltin builtinAgdaSort
primAgdaType     = getBuiltin builtinAgdaType
primAgdaTypeEl   = getBuiltin builtinAgdaTypeEl
primHiding       = getBuiltin builtinHiding
primHidden       = getBuiltin builtinHidden
primVisible      = getBuiltin builtinVisible
primRelvance     = getBuiltin builtinRelevance
primRelevant     = getBuiltin builtinRelevant
primIrrelevant   = getBuiltin builtinIrrelevant
primForced       = getBuiltin builtinForced
primAgdaSortSet  = getBuiltin builtinAgdaSortSet
primAgdaSortLit  = getBuiltin builtinAgdaSortLit
primAgdaSortUnsupported = getBuiltin builtinAgdaSortUnsupported
primAgdaTerm         = getBuiltin builtinAgdaTerm
primAgdaTermVar      = getBuiltin builtinAgdaTermVar
primAgdaTermLam      = getBuiltin builtinAgdaTermLam
primAgdaTermDef      = getBuiltin builtinAgdaTermDef
primAgdaTermCon      = getBuiltin builtinAgdaTermCon
primAgdaTermPi       = getBuiltin builtinAgdaTermPi
primAgdaTermSort     = getBuiltin builtinAgdaTermSort
primAgdaTermUnsupported     = getBuiltin builtinAgdaTermUnsupported
builtinNat          = "NATURAL"
builtinSuc          = "SUC"
builtinZero         = "ZERO"
builtinNatPlus      = "NATPLUS"
builtinNatMinus     = "NATMINUS"
builtinNatTimes     = "NATTIMES"
builtinNatDivSucAux = "NATDIVSUCAUX"
builtinNatModSucAux = "NATMODSUCAUX"
builtinNatEquals    = "NATEQUALS"
builtinNatLess      = "NATLESS"
builtinInteger      = "INTEGER"
builtinFloat        = "FLOAT"
builtinChar         = "CHAR"
builtinString       = "STRING"
builtinBool         = "BOOL"
builtinTrue         = "TRUE"
builtinFalse        = "FALSE"
builtinList         = "LIST"
builtinNil          = "NIL"
builtinCons         = "CONS"
builtinIO           = "IO"
builtinSize         = "SIZE"
builtinSizeSuc      = "SIZESUC"
builtinSizeInf      = "SIZEINF"
builtinInf          = "INFINITY"
builtinSharp        = "SHARP"
builtinFlat         = "FLAT"
builtinEquality     = "EQUALITY"
builtinRefl         = "REFL"
builtinLevelMax     = "LEVELMAX"
builtinLevel        = "LEVEL"
builtinLevelZero    = "LEVELZERO"
builtinLevelSuc     = "LEVELSUC"
builtinQName        = "QNAME"
builtinAgdaSort     = "AGDASORT"
builtinAgdaSortSet  = "AGDASORTSET"
builtinAgdaSortLit  = "AGDASORTLIT"
builtinAgdaSortUnsupported = "AGDASORTUNSUPPORTED"
builtinAgdaType     = "AGDATYPE"
builtinAgdaTypeEl   = "AGDATYPEEL"
builtinHiding       = "HIDING"
builtinHidden       = "HIDDEN"
builtinVisible      = "VISIBLE"
builtinRelevance    = "RELEVANCE"
builtinRelevant     = "RELEVANT"
builtinIrrelevant   = "IRRELEVANT"
builtinForced       = "FORCED"
builtinArg          = "ARG"
builtinArgArg       = "ARGARG"
builtinAgdaTerm         = "AGDATERM"
builtinAgdaTermVar      = "AGDATERMVAR"
builtinAgdaTermLam      = "AGDATERMLAM"
builtinAgdaTermDef      = "AGDATERMDEF"
builtinAgdaTermCon      = "AGDATERMCON"
builtinAgdaTermPi       = "AGDATERMPI"
builtinAgdaTermSort     = "AGDATERMSORT"
builtinAgdaTermUnsupported = "AGDATERMUNSUPPORTED"
